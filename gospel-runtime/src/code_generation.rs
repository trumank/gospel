use std::cell::RefCell;
use std::cmp::max;
use std::ops::{Deref};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use anyhow::bail;
use iced_x86::code_asm::*;
use region::{Allocation, Protection};
use gospel_typelib::type_model::{align_value, PrimitiveType, Type};
use crate::local_type_model::{CachedFunctionDescriptorData, TypeUniverse};

/// Dynamic code unwind table implementation for win32
#[cfg(windows)]
struct DynamicCodeUnwindTable {
    base_allocation_addr: *mut u8,
    function_table_handle: winapi::um::winnt::PVOID,
    function_table: Box<Vec<winapi::um::winnt::RUNTIME_FUNCTION>>,
    unwind_data_segment: PageRangeSegment,
    current_entry_count: usize,
    has_mapped_virtual_symbol_module: bool,
}
#[cfg(windows)]
impl DynamicCodeUnwindTable {
    fn get_unwind_data_segment_alignment() -> usize {
        // MSDN states that unwind info must be aligned to DWORD boundary
        size_of::<winapi::shared::minwindef::DWORD>()
    }
    fn calculate_unwind_data_page_count(num_code_pages: usize) -> usize {
        num_code_pages
    }
    fn allocate(base_allocation_addr: *mut u8, text_segment: &PageRangeSegment, unwind_data_segment: PageRangeSegment, register_virtual_sym_module: bool) -> Self {
        const AVERAGE_DYNAMIC_CODE_CHUNK_SIZE: usize = 64;
        let default_function_table_entry = unsafe { std::mem::zeroed::<winapi::um::winnt::RUNTIME_FUNCTION>() };
        let estimated_num_functions = max(text_segment.segment_length_bytes / AVERAGE_DYNAMIC_CODE_CHUNK_SIZE, 1);
        let mut function_table: Box<Vec<winapi::um::winnt::RUNTIME_FUNCTION>> = Box::new(vec![default_function_table_entry; estimated_num_functions]);
        let mut function_table_handle: winapi::um::winnt::PVOID = winapi::um::winnt::PVOID::default();
        let current_entry_count: usize = 0;

        let result_status = unsafe {
            winapi::um::winnt::RtlAddGrowableFunctionTable(
                &mut function_table_handle as *mut winapi::um::winnt::PVOID,
                function_table.as_mut_ptr(),
                current_entry_count as winapi::shared::minwindef::DWORD,
                function_table.len() as winapi::shared::minwindef::DWORD,
                base_allocation_addr.addr() as winapi::shared::basetsd::ULONG_PTR,
                text_segment.segment_end_addr.addr() as winapi::shared::basetsd::ULONG_PTR)
        };
        assert_eq!(result_status, winapi::shared::ntstatus::STATUS_SUCCESS as u32);

        let mut has_mapped_virtual_symbol_module = false;
        if register_virtual_sym_module {
            has_mapped_virtual_symbol_module = Self::register_virtual_symbol_module(base_allocation_addr, text_segment.segment_length_bytes);
        }
        Self{base_allocation_addr, function_table_handle, function_table, unwind_data_segment, current_entry_count, has_mapped_virtual_symbol_module}
    }
    fn can_add_unwind_info(&self, unwind_info_size: usize) -> bool {
        self.current_entry_count < self.function_table.len() &&
            self.unwind_data_segment.can_allocate_entry(unwind_info_size)
    }
    fn add_unwind_info(&mut self, text_start_addr: *mut u8, text_size_bytes: usize, unwind_info: &Vec<u8>) {
        assert!(self.can_add_unwind_info(unwind_info.len()));

        let new_unwind_info_addr = self.unwind_data_segment.allocate_entry(unwind_info);

        let relative_code_start_addr = text_start_addr.addr().checked_sub(self.base_allocation_addr.addr()).unwrap();
        let relative_code_end_addr = relative_code_start_addr + text_size_bytes;
        let relative_unwind_info_addr = new_unwind_info_addr.addr().checked_sub(self.base_allocation_addr.addr()).unwrap();
        Self::populate_runtime_function_info(&mut self.function_table[self.current_entry_count], relative_code_start_addr, relative_code_end_addr, relative_unwind_info_addr);
        self.current_entry_count += 1;
        unsafe { winapi::um::winnt::RtlGrowFunctionTable(self.function_table_handle, self.current_entry_count as winapi::shared::minwindef::DWORD); };
    }
    fn attach_symbol_to_function_entry(&mut self, text_start_addr: *mut u8, text_size_bytes: usize, symbol_name: &str) {
        if self.has_mapped_virtual_symbol_module {
            let base_of_dll = self.base_allocation_addr.addr() as winapi::shared::basetsd::ULONG64;
            let symbol_address = text_start_addr.addr() as winapi::shared::basetsd::DWORD64;
            let symbol_size = text_size_bytes as winapi::shared::minwindef::DWORD;
            let symbol_flags = 0 as winapi::shared::minwindef::DWORD;
            let symbol_name = std::ffi::CString::from_str(symbol_name).unwrap();

            // We call backtrace::resolve here with a fixed instruction pointer because we want backtrace-rs crate to do 2 things for us:
            // 1) acquire the global backtrace lock to avoid race conditions with other threads
            // 2) load and initialize DbgHelp with correct parameters
            // After that, inside the lambda we can safely access DbgHelp using FindLibrary and call the function to register our dynamic symbol
            let this_function_ip = Self::attach_symbol_to_function_entry as *mut core::ffi::c_void;
            let mut already_registered_symbol: bool = false;
            backtrace::resolve(this_function_ip, |_frame_symbol| {
                // Try our best not to panic here because we will most likely deadlock during backtrace printing since we are holding the dbghelp mutex
                if !already_registered_symbol {
                    already_registered_symbol = true;
                    let dbghelp_module_handle = unsafe { winapi::um::libloaderapi::GetModuleHandleA(b"dbghelp.dll\0".as_ptr() as *const i8) };
                    if dbghelp_module_handle != std::ptr::null_mut() {
                        // Find SymAddSymbol within the dbghelp DLL
                        let sym_add_symbol = unsafe { winapi::um::libloaderapi::GetProcAddress(dbghelp_module_handle, b"SymAddSymbol\0".as_ptr() as *const i8) };
                        if sym_add_symbol != std::ptr::null_mut() {
                            let current_process = unsafe { winapi::um::processthreadsapi::GetCurrentProcess() };
                            type SymAddSymbolPrototype = unsafe extern "C" fn(winapi::um::winnt::HANDLE, winapi::shared::basetsd::ULONG64, winapi::um::winnt::PCSTR,
                                                                              winapi::shared::basetsd::DWORD64, winapi::shared::minwindef::DWORD, winapi::shared::minwindef::DWORD) -> winapi::shared::minwindef::BOOL;
                            // Cast the function to the signature and register the symbol
                            let cast_sym_add_symbol = unsafe { std::mem::transmute::<winapi::shared::minwindef::FARPROC, SymAddSymbolPrototype>(sym_add_symbol) };
                            unsafe { cast_sym_add_symbol(current_process, base_of_dll, symbol_name.as_ptr(), symbol_address, symbol_size, symbol_flags); }
                        }
                    }
                }
            });
        }
    }
    fn register_virtual_symbol_module(base_allocation_addr: *mut u8, text_size_bytes: usize) -> bool {
        const SLMFLAG_VIRTUAL: u32 = 0x1;
        let module_name_c_str = std::ffi::CString::from_str(&format!("__gospel_runtime_dynamic_{:x}", base_allocation_addr.addr())).unwrap();
        let base_of_dll = base_allocation_addr.addr() as winapi::shared::basetsd::ULONG64;
        let dll_size = text_size_bytes as winapi::shared::minwindef::DWORD;
        let load_flags = SLMFLAG_VIRTUAL;

        // We call backtrace::resolve here with a fixed instruction pointer because we want backtrace-rs crate to do 2 things for us:
        // 1) acquire the global backtrace lock to avoid race conditions with other threads
        // 2) load and initialize DbgHelp with correct parameters
        // After that, inside the lambda we can safely access DbgHelp using FindLibrary and call the function to register our dynamic symbol
        let this_function_ip = Self::attach_symbol_to_function_entry as *mut core::ffi::c_void;
        let mut already_registered_module: bool = false;
        let mut module_registration_result: bool = false;
        backtrace::resolve(this_function_ip, |_frame_symbol| {
            // Try our best not to panic here because we will most likely deadlock during backtrace printing since we are holding the dbghelp mutex
            if !already_registered_module {
                already_registered_module = true;
                let dbghelp_module_handle = unsafe { winapi::um::libloaderapi::GetModuleHandleA(b"dbghelp.dll\0".as_ptr() as *const i8) };
                if dbghelp_module_handle != std::ptr::null_mut() {
                    // Find SymAddSymbol within the dbghelp DLL
                    let sym_load_module_ex = unsafe { winapi::um::libloaderapi::GetProcAddress(dbghelp_module_handle, b"SymLoadModuleEx\0".as_ptr() as *const i8) };
                    if sym_load_module_ex != std::ptr::null_mut() {
                        let current_process = unsafe { winapi::um::processthreadsapi::GetCurrentProcess() };
                        type SymLoadModuleExPrototype = unsafe extern "C" fn(winapi::um::winnt::HANDLE, winapi::um::winnt::HANDLE, winapi::um::winnt::PCSTR, winapi::um::winnt::PCSTR,
                            winapi::shared::basetsd::DWORD64, winapi::shared::minwindef::DWORD, winapi::shared::minwindef::LPVOID, winapi::shared::minwindef::DWORD) -> winapi::shared::basetsd::DWORD64;
                        // Cast the function to the signature and register the symbol
                        let cast_sym_load_module_ex = unsafe { std::mem::transmute::<winapi::shared::minwindef::FARPROC, SymLoadModuleExPrototype>(sym_load_module_ex) };
                        let return_value = unsafe { cast_sym_load_module_ex(current_process, std::ptr::null_mut(), std::ptr::null_mut(), module_name_c_str.as_ptr(), base_of_dll, dll_size, std::ptr::null_mut(), load_flags) };
                        module_registration_result = return_value == base_of_dll;
                    }
                }
            }
        });
        module_registration_result
    }
    #[cfg(not(target_arch = "aarch64"))]
    fn populate_runtime_function_info(function_info: &mut winapi::um::winnt::RUNTIME_FUNCTION, relative_code_start_addr: usize, relative_code_end_addr: usize, relative_unwind_info_addr: usize) {
        function_info.BeginAddress = relative_code_start_addr as winapi::shared::minwindef::DWORD;
        function_info.EndAddress = relative_code_end_addr as winapi::shared::minwindef::DWORD;
        *unsafe { function_info.u.UnwindInfoAddress_mut() } = relative_unwind_info_addr as winapi::shared::minwindef::DWORD;
    }
    #[cfg(target_arch = "aarch64")]
    fn populate_runtime_function_info(function_info: &mut winapi::um::winnt::RUNTIME_FUNCTION, relative_code_start_addr: usize, relative_code_end_addr: usize, relative_unwind_info_addr: usize) {
        function_info.BeginAddress = relative_code_start_addr as winapi::shared::minwindef::DWORD;
        // Since unwind info is aligned to DWORD boundary UnwindData refers to an RVA and not a packed unwind info
        function_info.UnwindData = relative_unwind_info_addr as winapi::shared::minwindef::DWORD;
    }
}

/// Dynamic code unwind stub implementation when unwinding support is not available for the current os
#[cfg(not(windows))]
struct DynamicCodeUnwindTable {}
#[cfg(not(windows))]
impl DynamicCodeUnwindTable {
    fn get_unwind_data_segment_alignment() -> usize { 1 }
    fn calculate_unwind_data_page_count(_num_code_pages: usize) -> usize { 1 }
    fn allocate(_base_allocation_addr: *mut u8, _text_segment: &PageRangeSegment, _unwind_data_segment: PageRangeSegment) -> Self {
        panic!("Unwind support not implemented for current target");
    }
    fn can_add_unwind_info(&self, _unwind_info_size: usize) -> bool { true }
    fn add_unwind_info(&mut self, _text_start_addr: *mut u8, _text_size_bytes: usize, _unwind_info: &Vec<u8>) {}
    fn attach_symbol_to_function_entry(&mut self, text_start_addr: *mut u8, text_size_bytes: usize, symbol_name: &str) {}
}

struct PageRangeSegment {
    segment_start_addr: *mut u8,
    segment_end_addr: *mut u8,
    segment_length_bytes: usize,
    segment_protection_flags: Protection,
    segment_entry_alignment: usize,
    first_free_addr: *mut u8,
}
impl PageRangeSegment {
    fn new_segment(parent_allocation: &mut Allocation, start_page_index: usize, num_pages: usize, protection_flags: Protection, entry_alignment: usize, fill_data: u8) -> Self {
        assert!(entry_alignment > 0);
        let single_page_size = region::page::size();
        let segment_start_offset_bytes = start_page_index * single_page_size;
        let segment_length_bytes = num_pages * single_page_size;

        let allocation_start_ptr = parent_allocation.as_mut_ptr::<u8>();
        let segment_start_addr = unsafe { allocation_start_ptr.byte_offset(segment_start_offset_bytes as isize) };
        let segment_end_addr = unsafe { segment_start_addr.byte_offset(segment_length_bytes as isize) };
        let segment_protection_flags = protection_flags;
        let segment_entry_alignment = entry_alignment;
        assert_eq!(segment_start_addr.addr() % segment_entry_alignment, 0);

        unsafe {
            let allocation_end_ptr = allocation_start_ptr.byte_offset(parent_allocation.len() as isize);
            assert!(segment_start_addr >= allocation_start_ptr && segment_end_addr <= allocation_end_ptr);

            region::protect(segment_start_addr, segment_length_bytes, Protection::READ_WRITE).unwrap();
            segment_start_addr.write_bytes(fill_data, segment_length_bytes);
            region::protect(segment_start_addr, segment_length_bytes, segment_protection_flags).unwrap();
        }
        Self{segment_start_addr, segment_end_addr, segment_length_bytes, segment_protection_flags, segment_entry_alignment, first_free_addr: segment_start_addr}
    }
    fn can_allocate_entry(&self, entry_size: usize) -> bool {
        let aligned_entry_size = (entry_size + (self.segment_entry_alignment - 1)) / self.segment_entry_alignment * self.segment_entry_alignment;
        let free_storage_size = self.segment_end_addr.addr().checked_sub(self.first_free_addr.addr()).unwrap_or(0);
        aligned_entry_size <= free_storage_size
    }
    fn allocate_entry(&mut self, entry_data: &Vec<u8>) -> *mut u8 {
        assert!(self.can_allocate_entry(entry_data.len()));

        let new_entry_start_addr = self.first_free_addr;
        let aligned_entry_size = (entry_data.len() + (self.segment_entry_alignment - 1)) / self.segment_entry_alignment * self.segment_entry_alignment;
        unsafe {
            region::protect(self.segment_start_addr, self.segment_length_bytes, Protection::READ_WRITE).unwrap();
            std::ptr::copy_nonoverlapping(entry_data.as_ptr(), new_entry_start_addr, entry_data.len());
            region::protect(self.segment_start_addr, self.segment_length_bytes, self.segment_protection_flags).unwrap();
        }
        self.first_free_addr = unsafe { self.first_free_addr.byte_offset(aligned_entry_size as isize) };
        new_entry_start_addr
    }
}

struct DynamicCodeChunk {
    text: Vec<u8>,
    unwind_info: Vec<u8>,
    symbol_name: Option<String>,
}
#[derive(Clone)]
pub(crate) struct CodeChunkReference {
    // Not actually dead, needed to keep weak pointers alive
    #[allow(dead_code)]
    owner_allocation: Rc<RefCell<DynamicCodeStorageAllocation>>,
    pub(crate) text_start_addr: *const u8,
}

struct DynamicCodeStorageAllocation {
    // Not actually dead, needed to keep weak pointers alive
    #[allow(dead_code)]
    page_range_allocation: Allocation,
    text_segment: PageRangeSegment,
    unwind_table: DynamicCodeUnwindTable,
}
impl DynamicCodeStorageAllocation {
    fn new_allocation(min_allocation_size: usize, register_virtual_sym_module: bool) -> Self {
        let single_page_size = region::page::size();
        let num_text_pages = max((min_allocation_size + (single_page_size - 1)) / single_page_size, 1);
        let num_unwind_data_pages = DynamicCodeUnwindTable::calculate_unwind_data_page_count(num_text_pages);

        let result_allocation_size = (num_text_pages + num_unwind_data_pages) * single_page_size;
        let mut page_range_allocation = region::alloc(result_allocation_size, Protection::READ_WRITE).unwrap();
        let base_address = page_range_allocation.as_mut_ptr::<u8>();

        let text_segment = PageRangeSegment::new_segment(&mut page_range_allocation, 0, num_text_pages, Protection::READ_EXECUTE, 1, 0xCC);
        let unwind_segment_alignment = DynamicCodeUnwindTable::get_unwind_data_segment_alignment();
        let unwind_data_segment = PageRangeSegment::new_segment(&mut page_range_allocation, num_text_pages, num_unwind_data_pages, Protection::READ, unwind_segment_alignment, 0);
        let unwind_table = DynamicCodeUnwindTable::allocate(base_address, &text_segment, unwind_data_segment, register_virtual_sym_module);

        Self{page_range_allocation, text_segment, unwind_table}
    }
    fn try_emplace_code_chunk(&mut self, chunk: &DynamicCodeChunk) -> Option<*mut u8> {
        if self.text_segment.can_allocate_entry(chunk.text.len()) && self.unwind_table.can_add_unwind_info(chunk.unwind_info.len()) {

            let text_start_addr = self.text_segment.allocate_entry(&chunk.text);
            self.unwind_table.add_unwind_info(text_start_addr, chunk.text.len(), &chunk.unwind_info);
            if let Some(symbol_name) = &chunk.symbol_name {
                self.unwind_table.attach_symbol_to_function_entry(text_start_addr, chunk.text.len(), symbol_name);
            }
            Some(text_start_addr)
        } else { None }
    }
}

#[derive(Default)]
struct ThreadLocalDynamicCodeStorage {
    all_allocations: Vec<Rc<RefCell<DynamicCodeStorageAllocation>>>,
}
impl ThreadLocalDynamicCodeStorage {
    thread_local! {
        static THREAD_CODE_STORAGE: RefCell<ThreadLocalDynamicCodeStorage> = RefCell::new(ThreadLocalDynamicCodeStorage::default());
    }
    fn register_symbols_for_dynamic_code_override() -> &'static AtomicBool {
        static OVERRIDE_REGISTER_SYMBOLS_FOR_DYNAMIC_CODE: AtomicBool = AtomicBool::new(false);
        &OVERRIDE_REGISTER_SYMBOLS_FOR_DYNAMIC_CODE
    }
    fn should_register_symbols_for_dynamic_code() -> bool {
        static SHOULD_REGISTER_SYMBOLS: AtomicU8 = AtomicU8::new(2);
        if SHOULD_REGISTER_SYMBOLS.load(Ordering::Acquire) == 2 {
            let backtrace_enabled = match std::env::var("RUST_LIB_BACKTRACE") {
                Ok(s) => s != "0",
                Err(_) => match std::env::var("RUST_BACKTRACE") { Ok(s) => s != "0", Err(_) => false }
            };
            let always_register_symbols = Self::register_symbols_for_dynamic_code_override().load(Ordering::Acquire);
            let new_value: u8 = if backtrace_enabled || always_register_symbols { 1 } else { 0 };
            let _ = SHOULD_REGISTER_SYMBOLS.compare_exchange(2, new_value, Ordering::AcqRel, Ordering::Acquire);
        }
        SHOULD_REGISTER_SYMBOLS.load(Ordering::Relaxed) == 1
    }
    fn link_code_chunk_private(&mut self, code_chunk: &DynamicCodeChunk) -> CodeChunkReference {
        for existing_page_allocation in &self.all_allocations {
            if let Some(result_code_ptr) = existing_page_allocation.borrow_mut().try_emplace_code_chunk(code_chunk) {
                return CodeChunkReference{owner_allocation: existing_page_allocation.clone(), text_start_addr: result_code_ptr};
            }
        }
        let new_page_allocation = Rc::new(RefCell::new(DynamicCodeStorageAllocation::new_allocation(code_chunk.text.len(), Self::should_register_symbols_for_dynamic_code())));
        self.all_allocations.push(new_page_allocation.clone());
        let result_code_ptr = new_page_allocation.borrow_mut().try_emplace_code_chunk(code_chunk).unwrap();
        CodeChunkReference{owner_allocation: new_page_allocation.clone(), text_start_addr: result_code_ptr}
    }
    fn link_code_chunk(code_chunk: &DynamicCodeChunk) -> CodeChunkReference {
        Self::THREAD_CODE_STORAGE.with_borrow_mut(|storage| storage.link_code_chunk_private(code_chunk))
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Win32ParameterType {
    ThisPointer,
    ReturnValueStorage,
    NormalParameter{parameter_index: usize, passed_to_thunk_as_pointer: bool},
}
#[derive(Copy, Clone)]
struct Win32ParameterPassData {
    pub pass_in_xmm_register: bool,
    pub pass_by_8byte_value: bool,
    pub parameter_value_width: usize,
    pub parameter_kind: Win32ParameterType,
}

/// Enables backtrace symbol names for dynamically generated code
pub fn enable_dynamic_code_backtraces() {
    ThreadLocalDynamicCodeStorage::register_symbols_for_dynamic_code_override().store(true, Ordering::Release);
}

#[cfg(all(windows, target_arch = "x86_64"))]
pub(crate) fn generate_virtual_function_call_thunk<TU: TypeUniverse>(function_desc: &CachedFunctionDescriptorData, write_return_value_to_return_value_storage: bool, by_value_parameter_passed_as_pointer: &[bool]) -> anyhow::Result<CodeChunkReference> {
    let readable_type_graph = TU::type_graph().read().unwrap();
    let base_return_type_index = readable_type_graph.base_type_index(function_desc.function_signature.return_value_type_index);

    // Determine how we should pass the function return value
    let (has_return_value, return_value_through_storage, return_value_width) = match readable_type_graph.type_by_index(base_return_type_index) {
        Type::Pointer(pointer_type) => (true, false, pointer_type.size_and_alignment(&TU::target_triplet())), // pointers are passed by value
        Type::Array(_) => bail!("Arrays cannot be returned from functions"),
        Type::CVQualified(_) => bail!("Did not expect CVQualified type as base type"),
        Type::Function(_) => bail!("Invalid function type as return value type"),
        Type::Enum(enum_type) => (true, false, enum_type.size_and_alignment(&TU::target_triplet())?), // enums are passed by value
        Type::Primitive(primitive_type) => {
            // primitives are passed by value, but void is not a valid return value
            if primitive_type != &PrimitiveType::Void {
                (true, false, primitive_type.size_and_alignment(&TU::target_triplet())?)
            } else { (false, false, 0) }
        },
        Type::UDT(user_defined_type) => {
            let type_layout = user_defined_type.layout(base_return_type_index, readable_type_graph.deref(), &mut TU::type_layout_cache().lock().unwrap().layout_cache)?;
            let udt_has_valid_size_to_pass_by_value = type_layout.size == 1 || type_layout.size == 2 || type_layout.size == 4 || type_layout.size == 8;
            let force_return_udt_by_ref = !udt_has_valid_size_to_pass_by_value ||
                type_layout.cpp_has_non_public_fields ||
                !type_layout.base_class_offsets.is_empty() ||
                !type_layout.resolved_cpp_type_traits.trivially_constructible ||
                !type_layout.resolved_cpp_type_traits.trivially_destructible ||
                !type_layout.resolved_cpp_type_traits.trivially_copy_constructible ||
                !type_layout.resolved_cpp_type_traits.trivially_move_constructible ||
                !type_layout.resolved_cpp_type_traits.trivially_copy_assignable;
            (true, force_return_udt_by_ref, type_layout.size)
        }
    };

    let mut result_function_parameters: Vec<Win32ParameterPassData> = Vec::new();

    // First parameter for virtual functions on win32 is always this pointer, even when using return value storage
    result_function_parameters.push(Win32ParameterPassData{
        pass_in_xmm_register: false,
        pass_by_8byte_value: true,
        parameter_value_width: TU::target_triplet().address_width(),
        parameter_kind: Win32ParameterType::ThisPointer,
    });

    // If we have a return value that must be returned through return value storage, add parameter for it before we add other parameters
    if has_return_value && return_value_through_storage {
        result_function_parameters.push(Win32ParameterPassData{
            pass_in_xmm_register: false,
            pass_by_8byte_value: true,
            parameter_value_width: TU::target_triplet().address_width(),
            parameter_kind: Win32ParameterType::ReturnValueStorage,
        });
    }

    // Generate parameter pass data for the rest of function parameters
    for parameter_index in 0..function_desc.function_signature.parameter_type_indices.len() {
        let base_parameter_type_index = readable_type_graph.base_type_index(function_desc.function_signature.parameter_type_indices[parameter_index]);
        let passed_to_thunk_as_pointer = parameter_index >= by_value_parameter_passed_as_pointer.len() || by_value_parameter_passed_as_pointer[parameter_index];
        let parameter_kind = Win32ParameterType::NormalParameter{parameter_index, passed_to_thunk_as_pointer};

        let parameter_pass_data = match readable_type_graph.type_by_index(base_parameter_type_index) {
            Type::Pointer(pointer_type) => Win32ParameterPassData{
                // pointers are passed by value in integer registers
                pass_in_xmm_register: false,
                pass_by_8byte_value: true,
                parameter_value_width: pointer_type.size_and_alignment(&TU::target_triplet()),
                parameter_kind,
            },
            Type::Array(array_type) => Win32ParameterPassData{
                // arrays are always passed as pointers, even if they fit in a register
                pass_in_xmm_register: false,
                pass_by_8byte_value: false,
                parameter_value_width: array_type.size_and_alignment(readable_type_graph.deref(), &mut TU::type_layout_cache().lock().unwrap().layout_cache)?.0,
                parameter_kind
            },
            Type::CVQualified(_) => bail!("Did not expect CVQualified type as base type"),
            Type::Function(_) => bail!("Invalid function type as parameter type"),
            Type::Enum(enum_type) => Win32ParameterPassData{
                // enums are passed by value in integer registers
                pass_in_xmm_register: false,
                pass_by_8byte_value: true,
                parameter_value_width: enum_type.size_and_alignment(&TU::target_triplet())?,
                parameter_kind
            },
            Type::Primitive(primitive_type) => Win32ParameterPassData{
                // primitives are passed by value, float and double are passed through xmm and the rest are passed in integer registers
                pass_in_xmm_register: primitive_type.is_floating_point(),
                pass_by_8byte_value: true,
                parameter_value_width: primitive_type.size_and_alignment(&TU::target_triplet())?,
                parameter_kind
            },
            Type::UDT(user_defined_type) => {
                let type_layout = user_defined_type.layout(base_return_type_index, readable_type_graph.deref(), &mut TU::type_layout_cache().lock().unwrap().layout_cache)?;
                let udt_has_valid_size_to_pass_by_value = type_layout.size == 1 || type_layout.size == 2 || type_layout.size == 4 || type_layout.size == 8;
                let force_pass_udt_by_ref = !udt_has_valid_size_to_pass_by_value || !type_layout.resolved_cpp_type_traits.trivially_copy_constructible;
                Win32ParameterPassData{
                    // UDTs are passed by value if they have a size of 1/2/4/8 bytes and a trivial copy constructor
                    pass_in_xmm_register: false,
                    pass_by_8byte_value: !force_pass_udt_by_ref,
                    parameter_value_width: type_layout.size,
                    parameter_kind
                }
            }
        };
        result_function_parameters.push(parameter_pass_data);
    }

    // We need stack space for home area for the first 4 register parameters + 8 bytes per each stack parameter (5th parameter and beyond)
    // Stack must also always be 16 byte aligned except for during the function prologue and epilogue. Since return address will make the stack not aligned
    // we need to reserve 8 extra bytes to keep the stack aligned and potentially write return value to
    let stack_parameter_size = 8;
    let stack_alignment = 16;
    let function_stack_allocation_size = (align_value(max(result_function_parameters.len(), 4) * stack_parameter_size, stack_alignment) + stack_parameter_size) as i32;

    let mut assembler = CodeAssembler::new(64)?;

    // Function prologue - allocate stack area for the function
    assembler.sub(rsp, function_stack_allocation_size)?;
    // We want to make sure prologue above is encoded as SUB r/m64, imm8, and not as SUB r/m64, imm32 because our unwind info expects
    // our stack allocation to be encodable with UWOP_ALLOC_SMALL, which can only encode stack allocations up to 128 bytes large
    assert!(function_stack_allocation_size >= i8::MIN as i32 && function_stack_allocation_size <= i8::MAX as i32);

    // Move return value storage ptr to the first 8 bytes of stack allocation
    // We might need to write to that pointer in case function returns by value but caller wants return by pointer
    assembler.mov(qword_ptr(rsp + (function_stack_allocation_size - 8)), rdx)?;

    // This pointer should stay in rcx, we will not overwrite it there
    // Move parameters_data from r8 to r10 since we will overwrite rcx/rdx/r8/r9 when preparing parameters
    assembler.mov(r10, r8)?;

    // Set up parameter registers and stack values now
    for parameter_index in 0..result_function_parameters.len() {
        let parameter_descriptor = &result_function_parameters[parameter_index];
        let parameter_width = parameter_descriptor.parameter_value_width;

        if parameter_descriptor.parameter_kind == Win32ParameterType::ThisPointer {
            // This pointer will always be the first argument of the member function call. It will be passed through rcx to the thunk,
            // which is the correct way to pass it to the target function as well
            assert_eq!(parameter_index, 0);
        }
        else if parameter_descriptor.parameter_kind == Win32ParameterType::ReturnValueStorage {
            // Return value storage, when used, must always be the second argument
            // If thunk passed return value storage as an argument, nothing needs to be done and rdx can just be forwarded to the target function as-is
            assert_eq!(parameter_index, 1);

            if !write_return_value_to_return_value_storage {
                // Special case, caller did not allocate return value storage in case where it should have been done
                // We can fix this by using first 8 bytes of the function stack allocation to temporarily store the return value
                // Later, after the original function call, we will load that value to rax to return it by value
                assert!(return_value_width <= 8);
                assembler.lea(rdx, qword_ptr(rsp + (function_stack_allocation_size - 8)))?;
                assembler.mov(qword_ptr(rdx), 0)?;
            }
        }
        else if let Win32ParameterType::NormalParameter { parameter_index: parameter_data_index, passed_to_thunk_as_pointer } = &parameter_descriptor.parameter_kind {
            let parameter_data_offset = (parameter_data_index * 8) as i32;
            let parameter_data_mem_no_size_hint = r10 + parameter_data_offset;

            // First 4 parameters are passed in either integer or floating point registers
            if parameter_index < 4 {
                let (move_target_register_1b, move_target_register_2b, move_target_register_4b, move_target_register_8b) = match parameter_index {
                    0 => (cl, cx, ecx, rcx),
                    1 => (dl, dx, edx, rdx),
                    2 => (r8b, r8w, r8d, r8),
                    3 => (r9b, r8w, r9d, r9),
                    _ => { bail!("Invalid parameter width for integer register: {}", parameter_width); }
                };

                if parameter_descriptor.pass_by_8byte_value {
                    // We are passing the parameters by value, not by pointer, so we need to use the correct register width
                    let move_source_mem = if *passed_to_thunk_as_pointer {
                        // load parameter point to rax so it can be loaded from rax by a later mov
                        assembler.mov(rax, qword_ptr(parameter_data_mem_no_size_hint))?;
                        rax.into()
                    } else {
                        // Best case scenario, we are passing parameter by value, and it has already been loaded by value
                        parameter_data_mem_no_size_hint
                    };

                    // Pick the correct instruction based on register width and whenever it is a floating point parameter
                    if parameter_descriptor.pass_in_xmm_register {
                        let move_target_register_xmm = match parameter_index {
                            0 => xmm0,
                            1 => xmm1,
                            2 => xmm2,
                            3 => xmm3,
                            _ => { bail!("Invalid parameter index {} passed in a register", parameter_index); }
                        };
                        // This parameter is passed in xmm registers, so we need to use movss/movsd to load it
                        match parameter_width {
                            4 => { assembler.movss(move_target_register_xmm, dword_ptr(move_source_mem))?; }
                            8 => { assembler.movsd_2(move_target_register_xmm, qword_ptr(move_source_mem))?; }
                            _ => { bail!("Invalid parameter width for xmm register: {}", parameter_width); }
                        };
                    } else {
                        // This is a normal integral parameter, so we need to use the regular mov for it
                        match parameter_width {
                            1 => { assembler.mov(move_target_register_1b, byte_ptr(move_source_mem))?; }
                            2 => { assembler.mov(move_target_register_2b, word_ptr(move_source_mem))?; }
                            4 => { assembler.mov(move_target_register_4b, dword_ptr(move_source_mem))?; }
                            8 => { assembler.mov(move_target_register_8b, qword_ptr(move_source_mem))?; }
                            _ => { bail!("Invalid parameter width for gp register: {}", parameter_width); }
                        };
                    }
                } else {
                    // We are passing this parameter as a pointer to an actual data storage and not by value
                    // That means we are inherently passing it in a gp register, not in xmm register
                    if *passed_to_thunk_as_pointer {
                        // If parameter is passed to the thunk by pointer, we just need to load the pointer into the destination register
                        assembler.mov(move_target_register_8b, qword_ptr(parameter_data_mem_no_size_hint))?;
                    } else {
                        // Otherwise, we need to point to the parameter value using lea. In this case the parameter size has to be smaller or equal to the stack slot size
                        assert!(parameter_width <= 8);
                        assembler.lea(move_target_register_8b, qword_ptr(parameter_data_mem_no_size_hint))?;
                    }
                }
            } else {
                // This is a 5th parameter or beyond, it is passed on the stack
                if parameter_descriptor.pass_by_8byte_value && *passed_to_thunk_as_pointer {
                    // Parameter needs to be passed by value to the function, but is passed by pointer to the thunk
                    // We need to load the pointer from the param data, read it into the register with the correct size,
                    // and then move the value from the register onto the stack
                    // Since target wants it passed by value, only valid sizes for the parameter are 1/2/4/8 bytes
                    assembler.mov(rax, qword_ptr(parameter_data_mem_no_size_hint))?;
                    match parameter_width {
                        1 => { assembler.mov(al, byte_ptr(rax))?; }
                        2 => { assembler.mov(ax, word_ptr(rax))?; }
                        4 => { assembler.mov(eax, dword_ptr(rax))?; }
                        8 => { assembler.mov(rax, qword_ptr(rax))?; }
                        _ => { bail!("Invalid parameter width for gp register: {}", parameter_width); }
                    };
                } else if !parameter_descriptor.pass_by_8byte_value && !*passed_to_thunk_as_pointer {
                    // Parameter needs to be passed as a pointer, but is passed to the thunk by value
                    // This can be fixed simply by pointing at the parameter data slot in the parameters vector as a pointer,
                    // and then giving that pointer to the target function
                    assembler.lea(rax, qword_ptr(parameter_data_mem_no_size_hint))?;
                } else {
                    // Parameter is passed by value/pointer to both the function and the thunk, just load it
                    // to a scratch register and then push it to the stack at correct offset
                    assembler.mov(rax, qword_ptr(parameter_data_mem_no_size_hint))?;
                }

                // Move value from the scratch register to its assigned slot on the stack
                let move_target_mem_no_size_hint = rsp + (parameter_index * 8) as i32;
                assembler.mov(qword_ptr(move_target_mem_no_size_hint), rax)?;
            }
        }
    }

    // Call the virtual function now using rax as a scratch register
    assembler.mov(rax, qword_ptr(rcx + function_desc.function_location.vtable_offset as i32))?;
    assembler.call(qword_ptr(rax + function_desc.function_location.offset as i32))?;

    if has_return_value {
        if write_return_value_to_return_value_storage && !return_value_through_storage {
            // This is a special case where calling convention declares that we must return by value, but the thunk descriptor wants the return value through return value storage
            // In this case we want to write current value of rax to return value storage buffer passed to us, and then update rax to point to the return value storage
            assembler.mov(rcx, qword_ptr(rsp + (function_stack_allocation_size - 8)))?;
            match return_value_width {
                1 => { assembler.mov(byte_ptr(rcx), al)?; }
                2 => { assembler.mov(word_ptr(rcx), ax)?; }
                4 => { assembler.mov(dword_ptr(rcx), eax)?; }
                8 => { assembler.mov(qword_ptr(rcx), rax)?; }
                _ => { bail!("Unsupported return value width for register: {}", return_value_width  ); }
            };
            // Set rax to point to the return value storage passed to the function
            assembler.mov(rax, rcx)?;
        } else if !write_return_value_to_return_value_storage && return_value_through_storage {
            // Opposite special case, calling convention wants value through storage but caller wants it returned through a pointer
            // In this case we have stored the return value in a return value storage stack slot, so we just need to load the value of that slot to rax
            assert!(return_value_width <= 8);
            assembler.mov(rax, qword_ptr(rsp + (function_stack_allocation_size - 8)))?;
        }
    } else {
        // If this function does not return a value, zero out rax to avoid having junk in the return value register
        assembler.xor(rax, rax)?;
    }

    // Function epilogue - trim function stack area and return
    assembler.add(rsp, function_stack_allocation_size)?;
    assembler.ret()?;

    // Assemble the thunk
    let result_code_buffer = assembler.assemble(0)?;

    // Generate unwind info for the thunk code we have just assembled
    let mut result_unwind_info: Vec<u8> = Vec::with_capacity(8);
    // UNWIND_INFO
    result_unwind_info.push(0x01); // version 1, flags 0 (no chained info, no termination handler, no exception handler)
    result_unwind_info.push(0x04); // size of prolog in bytes (SUB r/m64, imm8 in our case, which is 4 bytes as ensured by assert above)
    result_unwind_info.push(0x01); // count on unwind opcodes (we only need one)
    result_unwind_info.push(0x00); // frame register/frame offset (zero since we do not have a frame pointer)
    // UNWIND_CODE[0]
    result_unwind_info.push(0x04); // offset of instruction in the prolog (4 since our prolog is just 1 instruction)
    assert!(function_stack_allocation_size > 0 && function_stack_allocation_size % 8 == 0);
    let stack_allocation_size_encoded = (((function_stack_allocation_size - 8) / 8) as u8) & 0xF;
    result_unwind_info.push(0x02 | (stack_allocation_size_encoded << 4)); // UWOP_ALLOC_SMALL opcode (lower 4 bits) + encoded stack allocation size (upper 4 bits)
    // 2 padding bytes
    result_unwind_info.push(0x00);
    result_unwind_info.push(0x00);


    let linked_code_ref = ThreadLocalDynamicCodeStorage::link_code_chunk(&DynamicCodeChunk{text: result_code_buffer, unwind_info: result_unwind_info, symbol_name: Some(function_desc.function_name.clone())});
    Ok(linked_code_ref)
}