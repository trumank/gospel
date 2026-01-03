use crate::core_type_definitions::{implement_enum_underlying_type, implement_primitive_type_tag, EnumUnderlyingType, IntegralValueTypeTag, StaticTypeLayoutCache, StaticTypeTag};
use crate::code_generation::{generate_virtual_function_call_thunk, CodeChunkReference};
use generic_statics::{define_namespace, Namespace, Zeroable};
use gospel_typelib::compiled_target_triplet;
use gospel_typelib::target_triplet::TargetTriplet;
use gospel_typelib::type_model::{ArrayType, FunctionSignature, IntegerSignedness, MutableTypeGraph, PointerType, PrimitiveType, ResolvedUDTVirtualFunctionLocation, Type, UserDefinedTypeMember};
use std::alloc::{Allocator, Layout};
use std::clone::CloneToUninit;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::ptr::{null_mut, slice_from_raw_parts, slice_from_raw_parts_mut, NonNull, Pointee};
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};
use std::{mem, ptr};

pub use crate::code_generation::enable_dynamic_code_backtraces;

// Underlying type definitions for long int, unsigned long int and wide char depending on target platform
#[cfg(platform_long_size="4")]
pub type PlatformLongIntUnderlyingType = i32;
#[cfg(platform_long_size="8")]
pub type PlatformLongIntUnderlyingType = i64;

#[cfg(platform_long_size="4")]
pub type PlatformUnsignedLongIntUnderlyingType = u32;
#[cfg(platform_long_size="8")]
pub type PlatformUnsignedLongIntUnderlyingType = u64;

#[cfg(platform_wide_char_size="2")]
pub type PlatformWideCharUnderlyingType = u16;
#[cfg(platform_wide_char_size="4")]
pub type PlatformWideCharUnderlyingType = u32;

/// Represents a long int type with the bit width native to the running platform. Size can be either 4 or 8 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PlatformLongInt(PlatformLongIntUnderlyingType);

/// Represents an unsigned long int type with the bit width native to the running platform. Size can be either 4 or 8 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PlatformUnsignedLongInt(PlatformUnsignedLongIntUnderlyingType);

/// Represents a wide character type with the bit width native to the running platform. Size can be either 2 or 4 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PlatformWideChar(PlatformWideCharUnderlyingType);

implement_primitive_type_tag!(PlatformLongInt, PrimitiveType::LongInt);
implement_primitive_type_tag!(PlatformUnsignedLongInt, PrimitiveType::UnsignedLongInt);
implement_primitive_type_tag!(PlatformWideChar, PrimitiveType::WideChar);

implement_enum_underlying_type!(PlatformLongInt, PlatformLongIntUnderlyingType);
implement_enum_underlying_type!(PlatformUnsignedLongInt, PlatformUnsignedLongIntUnderlyingType);
implement_enum_underlying_type!(PlatformWideChar, PlatformWideCharUnderlyingType);

/// Returns the target triplet for which this module has been compiled
pub fn native_target_triplet() -> TargetTriplet {
    compiled_target_triplet().unwrap()
}

/// Type universe represents a contained type graph
pub trait TypeUniverse {
    fn target_triplet() -> TargetTriplet;
    fn type_graph() -> &'static RwLock<dyn MutableTypeGraph>;
    fn type_layout_cache() -> &'static Mutex<StaticTypeLayoutCache>;
}

/// Represents a mutable C++ reference (a non-null value pointer)
/// C++ References do not follow Rust reference semantics, and allow arbitrary mutation as well as sharing read and write access arbitrarily
/// C++ references implement Deref and DerefMut and can be temporarily converted to Rust references (immutable or otherwise)
/// This type transparently wraps a non-null byte pointer. Note that this implies that the pointer must be a thin pointer
/// Wide pointers are only supported if metadata can be derived statically from the value of the pointer as raw sequence of bytes
///
/// It is users responsibility to ensure that Rust reference semantics are followed when Deref and DerefMut are used. In general, avoid holding on to Rust references
/// and only use them to read/modify pointed value and/or call C++ functions on them. In all other cases, like storing the value in complex types,
/// prefer storing CRef value directly instead of storing a reference to ensure that Rust reference semantics are not violated
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct CRef<T : ?Sized> {
    raw_ptr: NonNull<()>,
    phantom_data: PhantomData<T>,
}
impl<T : ?Sized> CRef<T> {
    /// Creates a reference from a raw pointer. Will panic if the pointer is null
    pub fn from_raw_ptr(ptr: *const T) -> Self {
        Self{raw_ptr: NonNull::new(ptr as *mut ()).unwrap(), phantom_data: PhantomData::default()}
    }
    /// Creates an optional reference from a raw pointer
    pub fn from_raw_ptr_nullable(ptr: *const T) -> Option<Self> {
        if ptr.is_null() { None } else { Some(Self{raw_ptr: NonNull::new(ptr as *mut ()).unwrap(), phantom_data: PhantomData::default()}) }
    }
}

/// Implement this on DSTs that can have their metadata implicitly derived
pub trait ImplicitPtrMetadata : Pointee {
    /// Returns the metadata that can be implicitly created to determine the size of the value of this type
    /// Since ImplicitPtrMetadata can only be implemented for user-defined DSTs backed by a slice, this function should return the statically known size of the backing slice
    fn create_implicit_metadata() -> Self::Metadata;
    /// Returns the size of the value of this type, in bytes, using the implicit metadata
    fn static_size_of_val() -> usize {
        let null_ptr_with_metadata = ptr::from_raw_parts::<Self>(ptr::null::<()>(), Self::create_implicit_metadata());
        unsafe { mem::size_of_val_raw(null_ptr_with_metadata) }
    }
    /// Returns the alignment requirements for the value of this type, in bytes. Default implementation just uses align_of_val_raw, which might be incorrect if higher alignment is required
    fn static_align_of_val() -> usize {
        let null_ptr_with_metadata = ptr::from_raw_parts::<Self>(ptr::null::<()>(), Self::create_implicit_metadata());
        unsafe { mem::align_of_val_raw(null_ptr_with_metadata) }
    }
    /// Converts raw pointer of another type to the pointer to this type value
    fn from_raw_ptr<T: Pointee<Metadata = ()>>(ptr: *const T) -> *const Self {
        ptr::from_raw_parts::<Self>(ptr, Self::create_implicit_metadata())
    }
    /// Converts raw pointer of another type to the pointer to this type value
    fn from_raw_ptr_mut<T: Pointee<Metadata = ()>>(ptr: *mut T) -> *mut Self {
        ptr::from_raw_parts_mut::<Self>(ptr, Self::create_implicit_metadata())
    }
    /// Creates a null pointer to the object of this type
    fn null_ptr() -> *const Self {
        Self::from_raw_ptr(ptr::null::<u8>())
    }
    /// Creates a null pointer to the object of this type
    fn null_mut_ptr() -> *mut Self {
        Self::from_raw_ptr_mut(ptr::null_mut::<u8>())
    }
}
/// Default specialization for statically sized types which have no pointer metadata
impl<T : Pointee<Metadata = ()>> ImplicitPtrMetadata for T {
    fn create_implicit_metadata() -> Self::Metadata { () }
}

/// C references can be converted to wide pointers for DSTs with statically known (implicit) metadata
impl<T : ?Sized + ImplicitPtrMetadata> CRef<T> {
    /// Converts this C reference to a raw pointer to the underlying value
    pub fn as_ptr(&self) -> *const T {
        ptr::from_raw_parts::<T>(self.raw_ptr.as_ptr(), T::create_implicit_metadata())
    }
    /// Converts this C reference to a raw pointer to the underlying value
    pub fn as_mut_ptr(&mut self) -> *mut T {
        ptr::from_raw_parts_mut::<T>(self.raw_ptr.as_ptr(), T::create_implicit_metadata())
    }
}

/// Implementation of Deref for references to implicitly sized dynamically sized types
impl<T: ?Sized + ImplicitPtrMetadata> Deref for CRef<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.as_ptr().as_ref().unwrap() }
    }
}
/// Implementation of DerefMut for references to implicitly sized dynamically sized types
impl<T : ?Sized + ImplicitPtrMetadata> DerefMut for CRef<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.as_mut_ptr().as_mut().unwrap() }
    }
}
/// Static type tag implementation for C reference type
impl<T : ?Sized + ImplicitPtrMetadata + StaticTypeTag> StaticTypeTag for CRef<T> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: true}))
    }
}
/// Reference type wrapped in Option is a pointer
impl<T : ?Sized + ImplicitPtrMetadata + StaticTypeTag> StaticTypeTag for Option<CRef<T>> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: false}))
    }
}

/// Direct access functions implemented for bitwise copyable types
impl<T : Copy> CRef<T> {
    /// Performs a bitwise copy of the given value from the pointer
    pub fn read(&self) -> T {
        unsafe { ptr::read(self.as_ptr()) }
    }
    /// Writes a bitwise copy of the given value to the pointer
    pub fn write(&mut self, value: T) {
        unsafe { ptr::write(self.as_mut_ptr(), value) }
    }
}

/// Trait that allows dynamically sized types to be default-constructed at the arbitrary memory location represented as a pointer
pub unsafe trait DefaultConstructAtUninit {
    /// Called to construct the value of this type at the given memory location
    unsafe fn default_construct_at(dest: *mut u8);
}
/// Default specialization of DefaultConstructAtUninit for sized types with Default value
unsafe impl<T : Default> DefaultConstructAtUninit for T {
    unsafe fn default_construct_at(dest: *mut u8) {
        let result_ptr = dest as *mut T;
        unsafe { result_ptr.write(T::default()); }
    }
}

/// Allocates a slice of memory using the size and alignment requirements of the given type
pub fn allocate_uninitialized<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: &A) -> *mut u8 {
    alloc.allocate(Layout::from_size_align(T::static_size_of_val(), T::static_align_of_val()).unwrap()).unwrap().as_ptr() as *mut u8
}

/// Allocates a slice of memory using the size and alignment requirements of the given type. Function is not safe because it does not ensure that zeroed out memory is a valid value of type T
pub unsafe fn allocate_zeroed<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: &A) -> NonNull<T> {
    let result_ptr = allocate_uninitialized::<T, A>(alloc);
    unsafe { result_ptr.write_bytes(0, T::static_size_of_val()) };
    NonNull::new(ptr::from_raw_parts_mut(result_ptr, T::create_implicit_metadata())).unwrap()
}

/// Allocates a default instance of the given type and returns a raw pointer to it. Value must be manually dropped and memory freed
pub fn allocate_default_raw<T : ?Sized + ImplicitPtrMetadata + DefaultConstructAtUninit, A : Allocator>(alloc: &A) -> NonNull<T> {
    let value_storage_memory = allocate_uninitialized::<T, A>(alloc);
    unsafe { T::default_construct_at(value_storage_memory); }
    NonNull::new(ptr::from_raw_parts_mut(value_storage_memory, T::create_implicit_metadata())).unwrap()
}

/// Allocates a default instance of the given type and returns a box owning the value
pub fn allocate_default<T : ?Sized + ImplicitPtrMetadata + DefaultConstructAtUninit, A : Allocator>(alloc: A) -> Box<T, A> {
    let owned_ptr = allocate_default_raw::<T, A>(&alloc);
    unsafe { Box::<T, A>::from_non_null_in(owned_ptr, alloc) }
}

/// Clones the reference to the unsized value to the memory location allocated from the given allocator. Returns a raw pointer to the resulting value. Value must be manually dropped and memory freed
pub fn clone_unsized_raw<T : ?Sized + ImplicitPtrMetadata + CloneToUninit, A : Allocator>(src: &T, alloc: &A) -> NonNull<T> {
    let dest_memory = allocate_uninitialized::<T, A>(alloc);
    unsafe { src.clone_to_uninit(dest_memory); }
    NonNull::new(ptr::from_raw_parts_mut(dest_memory, T::create_implicit_metadata())).unwrap()
}

/// Clones the reference to the unsized value to the memory location allocated from the given allocator and returns a box owning the value
pub fn clone_unsized<T : ?Sized + ImplicitPtrMetadata + CloneToUninit, A : Allocator>(src: &T, alloc: A) -> Box<T, A> {
    let owned_ptr = clone_unsized_raw::<T, A>(src, &alloc);
    unsafe { Box::<T, A>::from_non_null_in(owned_ptr, alloc) }
}

/// Attempts to cast a reference to value of From type to a reference to value of To type. Returns None if the cast is not possible
pub fn static_cast<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: &From) -> Option<&To> {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast(src)
}

/// Attempts to cast a reference to value of From type to a reference to value of To type. Panics if the cast is not possible
pub fn static_cast_checked<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: &From) -> &To {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast(src).unwrap()
}

/// Attempts to cast a mutable reference to value of From type to a reference to value of To type. Returns None if the cast is not possible
pub fn static_cast_mut<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: &mut From) -> Option<&mut To> {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_mut(src)
}

/// Attempts to cast a mutable reference to value of From type to a reference to value of To type. Panics if the cast is not possible
pub fn static_cast_mut_checked<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: &mut From) -> &mut To {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_mut(src).unwrap()
}

/// Attempts to cast a pointer to value of From type to a reference to value of To type. Returns None if the cast is not possible
pub fn static_cast_ptr<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: *const From) -> Option<*const To> {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_ptr(src)
}

/// Attempts to cast a pointer to value of From type to a reference to value of To type. Panics if the cast is not possible
pub fn static_cast_ptr_checked<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: *const From) -> *const To {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_ptr(src).unwrap()
}

/// Attempts to cast a pointer to value of From type to a reference to value of To type. Returns None if the cast is not possible
pub fn static_cast_ptr_mut<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: *mut From) -> Option<*mut To> {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_ptr_mut(src)
}

/// Attempts to cast a pointer to value of From type to a reference to value of To type. Panics if the cast is not possible
pub fn static_cast_ptr_mut_checked<From: ?Sized + StaticTypeTag + 'static, To: ?Sized + ImplicitPtrMetadata + StaticTypeTag + 'static, TU: TypeUniverse + 'static>(src: *mut From) -> *mut To {
    define_namespace!(CastDescriptor);
    CastDescriptor::generic_static::<CachedThreadSafeStaticCastThisAdjust<From, To, TU>>().static_cast_ptr_mut(src).unwrap()
}

/// Represents a statically sized C or C++ array, which is a linear sequence of values of type T
pub struct StaticArray<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> {
    phantom_data_array_count: PhantomData<N>,
    phantom_data_element_type: PhantomData<T>,
    private_bytes: [u8],
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> StaticArray<T, N> {
    /// Returns the length of this statically sized array
    pub fn static_len() -> usize {
        N::get_raw_integral_value() as usize
    }
    /// Returns the length of this array
    pub fn len(&self) -> usize {
        Self::static_len()
    }
    /// Returns a const pointer to the array element at index. Will panic if index is out of bounds
    pub fn element_ptr(&self, index: usize) -> *const T {
        assert!(index < Self::static_len());
        let data_ptr = unsafe { self.private_bytes.as_ptr().byte_offset((T::static_size_of_val() * index) as isize) };
        ptr::from_raw_parts::<T>(data_ptr, T::create_implicit_metadata())
    }
    /// Returns a mut pointer to the array element at index. Will panic if index is out of bounds
    pub fn element_mut_ptr(&mut self, index: usize) -> *mut T {
        assert!(index < Self::static_len());
        let data_ptr = unsafe { self.private_bytes.as_mut_ptr().offset((T::static_size_of_val() * index) as isize) };
        ptr::from_raw_parts_mut::<T>(data_ptr, T::create_implicit_metadata())
    }
}
impl<T : ImplicitPtrMetadata, N : IntegralValueTypeTag> ImplicitPtrMetadata for StaticArray<T, N> {
    fn create_implicit_metadata() -> Self::Metadata {
        T::static_size_of_val() * Self::static_len() // array DST size is size of the element multiplied by the number of elements
    }
    fn static_align_of_val() -> usize {
        T::static_align_of_val() // copy the alignment from our element type
    }
}
impl<T : ImplicitPtrMetadata, N : IntegralValueTypeTag> Drop for StaticArray<T, N> {
    fn drop(&mut self) {
        // Execute destructor for each array element
        for index in 0..Self::static_len() {
            unsafe { self.element_mut_ptr(index).drop_in_place() }
        }
    }
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> Index<usize> for StaticArray<T, N> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.element_ptr(index).as_ref().unwrap() }
    }
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> IndexMut<usize> for StaticArray<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.element_mut_ptr(index).as_mut().unwrap() }
    }
}
impl<T : StaticTypeTag + ImplicitPtrMetadata, N: IntegralValueTypeTag> StaticTypeTag for StaticArray<T, N> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let element_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let array_length = N::get_raw_integral_value() as usize;
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Array(ArrayType{element_type_index, array_length}))
    }
}
unsafe impl<T : StaticTypeTag + ImplicitPtrMetadata + DefaultConstructAtUninit, N : IntegralValueTypeTag> DefaultConstructAtUninit for StaticArray<T, N> {
    unsafe fn default_construct_at(dest: *mut u8) {
        // Call default constructor on each individual array element
        for index in 0..Self::static_len() {
            let element_ptr = unsafe { dest.byte_offset((T::static_size_of_val() * index) as isize) };
            unsafe { T::default_construct_at(element_ptr); }
        }
    }
}

/// Represents a reference to a value of opaque type with the given lifetime and the specified type index in the given type universe
pub struct DynRef<'a, TU : TypeUniverse> {
    opaque_value: &'a [u8],
    type_index: usize,
    type_universe_phantom_data: PhantomData<TU>,
}
impl<'a, TU : TypeUniverse> DynRef<'a, TU> {
    /// Attempts to cast the value referenced by this dynamic reference to the given type
    pub fn static_cast<T : StaticTypeTag + ImplicitPtrMetadata>(&self) -> Option<&'a T> {
        let to_type_index = T::store_type_descriptor_to_universe::<TU>();
        let this_pointer_adjust = TU::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(TU::type_graph(), self.type_index, to_type_index)?;
        let adjusted_raw_this_ptr = unsafe { self.opaque_value.as_ptr().byte_offset(this_pointer_adjust as isize) };
        let adjusted_this_ptr = ptr::from_raw_parts::<T>(adjusted_raw_this_ptr, T::create_implicit_metadata());
        Some(unsafe { adjusted_this_ptr.as_ref_unchecked::<'a>() })
    }
    /// Retrieves the pointer to the raw value data from the reference
    pub fn as_raw_ptr(&self) -> *const u8 {
        self.opaque_value.as_ptr()
    }
    /// Returns the index of the type from the owning type universe that describes the value pointed to by this reference
    pub fn type_index(&self) -> usize {
        self.type_index
    }
    /// Constructs a dynamic reference from the given memory location and type index.
    /// Safety: raw_ptr must point to a value of type described by type_index. Pointer must be valid for the lifetime of the returned DynMut object and have correct provenance
    pub unsafe fn from_raw_parts(raw_ptr: *const u8, type_index: usize) -> Self {
        let (type_size, _) = TU::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(TU::type_graph(), type_index);
        Self{opaque_value: unsafe { &*slice_from_raw_parts(raw_ptr, type_size) }, type_index, type_universe_phantom_data: PhantomData::default()}
    }
}
/// Dynamic references can be constructed from normal references to tagged types
impl<'a, TU : TypeUniverse, T : StaticTypeTag + ImplicitPtrMetadata> From<&'a T> for DynRef<'a, TU> {
    fn from(value: &'a T) -> Self {
        Self{
            opaque_value: unsafe { &*slice_from_raw_parts(value as *const T as *const u8, T::static_size_of_val()) },
            type_index: T::store_type_descriptor_to_universe::<TU>(),
            type_universe_phantom_data: PhantomData::default(),
        }
    }
}

/// Represents a mutable reference to a value of opaque type with the given lifetime and the specified type index in the given type universe
pub struct DynMut<'a, TU : TypeUniverse> {
    opaque_value: &'a mut [u8],
    type_index: usize,
    type_universe_phantom_data: PhantomData<TU>,
}
impl<'a, TU : TypeUniverse> DynMut<'a, TU> {
    /// Attempts to cast the value referenced by this dynamic reference to the given type
    pub fn static_cast<T : StaticTypeTag + ImplicitPtrMetadata>(&mut self) -> Option<&'a mut T> {
        let to_type_index = T::store_type_descriptor_to_universe::<TU>();
        let this_pointer_adjust = TU::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(TU::type_graph(), self.type_index, to_type_index)?;

        let adjusted_raw_this_ptr = unsafe { self.opaque_value.as_mut_ptr().byte_offset(this_pointer_adjust as isize) };
        let adjusted_this_ptr = ptr::from_raw_parts_mut::<T>(adjusted_raw_this_ptr, T::create_implicit_metadata());
        Some(unsafe { adjusted_this_ptr.as_mut_unchecked::<'a>() })
    }
    /// Retrieves the pointer to the raw value data from the mutable reference
    pub fn as_raw_ptr(&mut self) -> *mut u8 {
        self.opaque_value.as_mut_ptr()
    }
    /// Returns the index of the type from the owning type universe that describes the value pointed to by this reference
    pub fn type_index(&self) -> usize {
        self.type_index
    }
    /// Constructs a dynamic mutable reference from the given memory location and type index.
    /// Safety: raw_ptr must point to a value of type described by type_index. Pointer must be valid for the lifetime of the returned DynMut object and have correct provenance
    pub unsafe fn from_raw_parts(raw_ptr: *mut u8, type_index: usize) -> Self {
        let (type_size, _) = TU::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(TU::type_graph(), type_index);
        Self{opaque_value: unsafe { &mut *slice_from_raw_parts_mut(raw_ptr, type_size) }, type_index, type_universe_phantom_data: PhantomData::default()}
    }
}
/// Dynamic mutable references can be constructed from normal references to tagged types
impl<'a, TU : TypeUniverse, T : StaticTypeTag + ImplicitPtrMetadata> From<&'a mut T> for DynMut<'a, TU> {
    fn from(value: &'a mut T) -> Self {
        Self{
            opaque_value: unsafe { &mut *slice_from_raw_parts_mut(value as *mut T as *mut u8, T::static_size_of_val()) },
            type_index: T::store_type_descriptor_to_universe::<TU>(),
            type_universe_phantom_data: PhantomData::default(),
        }
    }
}

/// Calculates size of the given type with the static type tag in the given type universe
pub fn calc_type_size_and_alignment<T : StaticTypeTag, U : TypeUniverse>() -> (usize, usize) {
    let type_index = T::store_type_descriptor_to_universe::<U>();
    U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), type_index)
}

/// Calculates the value of the enum constant with the given name
pub fn calc_enum_constant_value<T : StaticTypeTag, U : TypeUniverse>(constant_name: &'static str) -> Option<u64> {
    let type_index = T::store_type_descriptor_to_universe::<U>();
    U::type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(U::type_graph(), type_index, constant_name)
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeTypeSizeAndAlignment<T: ?Sized + StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    type_size: AtomicUsize,
    type_alignment: AtomicUsize,
    is_enum_type: AtomicBool,
    is_enum_underlying_type_signed: AtomicBool,
    _phantom_data_type: PhantomData<T>,
    _phantom_data_type_universe: PhantomData<U>,
}
unsafe impl<T: ?Sized + StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeTypeSizeAndAlignment<T, U> {}
impl<T: ?Sized + StaticTypeTag, U : TypeUniverse> CachedThreadSafeTypeSizeAndAlignment<T, U> {
    pub fn get_type_size_and_alignment(&self) -> (usize, usize) {
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();
            let (type_size, type_alignment) = U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), type_index);
            let (is_enum_type, is_underlying_type_signed) = if let Type::Enum(enum_type) = U::type_graph().read().unwrap().type_by_index(type_index).clone() {
                (true, enum_type.underlying_type(&U::target_triplet()).unwrap().integer_signedness().unwrap() == IntegerSignedness::Signed)
            } else { (false, false) };
            self.is_enum_type.store(is_enum_type, Ordering::Relaxed);
            self.is_enum_underlying_type_signed.store(is_underlying_type_signed, Ordering::Relaxed);
            self.type_size.store(type_size, Ordering::Relaxed);
            self.type_alignment.store(type_alignment, Ordering::Relaxed);
            self.has_value_cached.store(true, Ordering::Release);
        }
        (self.type_size.load(Ordering::Relaxed), self.type_alignment.load(Ordering::Relaxed))
    }
}
impl<T : ?Sized + StaticTypeTag + ImplicitPtrMetadata, U : TypeUniverse> CachedThreadSafeTypeSizeAndAlignment<T, U> {
    /// Creates an enum value initialized from the raw discriminant in the given allocator
    pub fn create_boxed_enum_value<A: Allocator>(&self, raw_discriminant: u64, alloc: A) -> Box<T, A> {
        // Although type size could also be derived from ImplicitPtrMetadata, we have to call get_type_size_and_alignment to calculate enum-specific fields
        let (underlying_type_size, _) = self.get_type_size_and_alignment();
        assert!(self.is_enum_type.load(Ordering::Relaxed));
        let is_underlying_type_signed = self.is_enum_underlying_type_signed.load(Ordering::Relaxed);

        let raw_value_ptr = allocate_uninitialized::<T, A>(&alloc);
        match is_underlying_type_signed {
            true => match underlying_type_size {
                1 => unsafe { (raw_value_ptr as *mut i8).write(i8::from_raw_discriminant(raw_discriminant)); }
                2 => unsafe { (raw_value_ptr as *mut i16).write(i16::from_raw_discriminant(raw_discriminant)); }
                4 => unsafe { (raw_value_ptr as *mut i32).write(i32::from_raw_discriminant(raw_discriminant)); }
                8 => unsafe { (raw_value_ptr as *mut i64).write(i64::from_raw_discriminant(raw_discriminant)); }
                _ => { unreachable!(); }
            }
            false => match underlying_type_size {
                1 => unsafe { raw_value_ptr.write(u8::from_raw_discriminant(raw_discriminant)); }
                2 => unsafe { (raw_value_ptr as *mut u16).write(u16::from_raw_discriminant(raw_discriminant)); }
                4 => unsafe { (raw_value_ptr as *mut u32).write(u32::from_raw_discriminant(raw_discriminant)); }
                8 => unsafe { (raw_value_ptr as *mut u64).write(u64::from_raw_discriminant(raw_discriminant)); }
                _ => { unreachable!(); }
            }
        };
        let value_ptr = ptr::from_raw_parts_mut::<T>(raw_value_ptr, T::create_implicit_metadata());
        unsafe { Box::from_raw_in(value_ptr, alloc) }
    }
    /// Reads an enum value into a raw discriminant value
    pub fn read_boxed_enum_value(&self, enum_value: &T) -> u64 {
        // Although type size could also be derived from ImplicitPtrMetadata, we have to call get_type_size_and_alignment to calculate enum-specific fields
        let (underlying_type_size, _) = self.get_type_size_and_alignment();
        assert!(self.is_enum_type.load(Ordering::Relaxed));
        let is_underlying_type_signed = self.is_enum_underlying_type_signed.load(Ordering::Relaxed);
        let raw_enum_value_ptr = enum_value as *const T;

        match is_underlying_type_signed {
            true => match underlying_type_size {
                1 => unsafe { (raw_enum_value_ptr as *const i8).read().to_raw_discriminant() }
                2 => unsafe { (raw_enum_value_ptr as *const i16).read().to_raw_discriminant() }
                4 => unsafe { (raw_enum_value_ptr as *const i32).read().to_raw_discriminant() }
                8 => unsafe { (raw_enum_value_ptr as *const i64).read().to_raw_discriminant() }
                _ => { unreachable!(); }
            }
            false => match underlying_type_size {
                1 => unsafe { (raw_enum_value_ptr as *const u8).read().to_raw_discriminant() }
                2 => unsafe { (raw_enum_value_ptr as *const u16).read().to_raw_discriminant() }
                4 => unsafe { (raw_enum_value_ptr as *const u32).read().to_raw_discriminant() }
                8 => unsafe { (raw_enum_value_ptr as *const u64).read().to_raw_discriminant() }
                _ => { unreachable!(); }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeStaticCastThisAdjust<From : ?Sized + StaticTypeTag, To: ?Sized + StaticTypeTag + ImplicitPtrMetadata, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_cast_possible: AtomicBool,
    cast_this_adjust: AtomicIsize,
    _phantom_data_from: PhantomData<From>,
    _phantom_data_to: PhantomData<To>,
    _phantom_data_type_universe: PhantomData<U>,
}
unsafe impl<From : ?Sized + StaticTypeTag, To: ?Sized + StaticTypeTag + ImplicitPtrMetadata, U : TypeUniverse> Zeroable for CachedThreadSafeStaticCastThisAdjust<From, To, U> {}
impl<From : ?Sized + StaticTypeTag, To: ?Sized + StaticTypeTag + ImplicitPtrMetadata, U : TypeUniverse> CachedThreadSafeStaticCastThisAdjust<From, To, U> {
    pub fn get_static_cast_this_adjust(&self) -> Option<isize> {
        if !self.has_value_cached.load(Ordering::Acquire) {
            let from_type_index = From::store_type_descriptor_to_universe::<U>();
            let to_type_index = To::store_type_descriptor_to_universe::<U>();
            if let Some(static_cast_adjust) = U::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(U::type_graph(), from_type_index, to_type_index) {
                self.result_cast_possible.store(true, Ordering::Relaxed);
                self.cast_this_adjust.store(static_cast_adjust as isize, Ordering::Relaxed);
            } else {
                self.result_cast_possible.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        if self.result_cast_possible.load(Ordering::Relaxed) {
            Some(self.cast_this_adjust.load(Ordering::Relaxed))
        } else { None }
    }
    /// Attempts to cast a reference to type From to a reference to type To. Returns resulting reference on success, or None if cast is not possible
    pub fn static_cast<'a>(&self, from: &'a From) -> Option<&'a To> {
        let static_cast_adjust = self.get_static_cast_this_adjust()?;
        Some(unsafe { To::from_raw_ptr((from as *const From as *const u8).byte_offset(static_cast_adjust)).as_ref_unchecked::<'a>() })
    }
    /// Attempts to cast a mutable reference to type From to a reference to type To. Returns resulting reference on success, or None if cast is not possible
    pub fn static_cast_mut<'a>(&self, from: &'a mut From) -> Option<&'a mut To> {
        let static_cast_adjust = self.get_static_cast_this_adjust()?;
        Some(unsafe { To::from_raw_ptr_mut((from as *mut From as *mut u8).byte_offset(static_cast_adjust)).as_mut_unchecked::<'a>() })
    }
    /// Attempts to cast a pointer to type From to a pointer to type To. Returns resulting pointer on success, or None if cast is not possible
    pub fn static_cast_ptr(&self, from: *const From) -> Option<*const To> {
        let static_cast_adjust = self.get_static_cast_this_adjust()?;
        Some(unsafe { To::from_raw_ptr((from as *const u8).byte_offset(static_cast_adjust)) })
    }
    /// Attempts to cast a mut pointer to type From to a pointer to type To. Returns resulting pointer on success, or None if cast is not possible
    pub fn static_cast_ptr_mut(&self, from: *mut From) -> Option<*mut To> {
        let static_cast_adjust = self.get_static_cast_this_adjust()?;
        Some(unsafe { To::from_raw_ptr_mut((from as *mut u8).byte_offset(static_cast_adjust)) })
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeFieldTypeAndOffset<T : ?Sized + StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_has_field: AtomicBool,
    field_type_index: AtomicUsize,
    field_offset_bytes: AtomicUsize,
    field_size_bytes: AtomicUsize,
    _phantom_udt_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
unsafe impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeFieldTypeAndOffset<T, U> {}
impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> CachedThreadSafeFieldTypeAndOffset<T, U> {
    pub fn get_field_type_index_offset_and_size(&self, field_name: &'static str) -> Option<(usize, usize, usize)> {
        // If there is no value cached, we have to calculate the value here and then release the has_value_cached to make the results visible to other threads
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();

            // We want relaxed ordering here since they will be ordered by has_value_cached anyway
            let field_type_and_offset = U::type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(U::type_graph(), type_index, field_name);
            if let Some((field_type_index, field_offset_bytes)) = field_type_and_offset {
                let field_size_bytes = U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), field_type_index).0;
                self.result_has_field.store(true, Ordering::Relaxed);
                self.field_type_index.store(field_type_index, Ordering::Relaxed);
                self.field_offset_bytes.store(field_offset_bytes, Ordering::Relaxed);
                self.field_size_bytes.store(field_size_bytes, Ordering::Relaxed);
            } else {
                self.result_has_field.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        if self.result_has_field.load(Ordering::Relaxed) {
            Some((self.field_type_index.load(Ordering::Relaxed), self.field_offset_bytes.load(Ordering::Relaxed), self.field_size_bytes.load(Ordering::Relaxed)))
        } else { None }
    }
    /// Returns the reference to the field with the given name from the base reference and the field name
    pub fn get_field_ref<'a, F : ?Sized + ImplicitPtrMetadata>(&self, base_ref: &'a T, field_name: &'static str) -> Option<&'a F> {
        let (_, field_offset_bytes, _) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *const T as *const u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts::<F>(field_raw_ptr, F::create_implicit_metadata());
        Some(unsafe { field_ptr.as_ref_unchecked::<'a>() })
    }
    /// Returns the mutable reference to the field with the given name from the base reference and the field name
    pub fn get_field_mut<'a, F : ?Sized + ImplicitPtrMetadata>(&self, base_ref: &'a mut T, field_name: &'static str) -> Option<&'a mut F> {
        let (_, field_offset_bytes, _) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *mut T as *mut u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts_mut::<F>(field_raw_ptr, F::create_implicit_metadata());
        Some(unsafe { field_ptr.as_mut_unchecked::<'a>() })
    }
    /// Returns the dynamic reference to the field with the given name from the base reference and the field name
    pub fn get_dyn_ref<'a>(&self, base_ref: &'a T, field_name: &'static str) -> Option<DynRef<'a, U>> {
        let (field_type_index, field_offset_bytes, field_size_bytes) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *const T as *const u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts::<[u8]>(field_raw_ptr, field_size_bytes);
        Some(DynRef{opaque_value: unsafe { field_ptr.as_ref_unchecked::<'a>() }, type_index: field_type_index, type_universe_phantom_data: PhantomData::default()})
    }
    /// Returns the mutable dynamic reference to the field with the given name from the base reference and the field name
    pub fn get_dyn_mut<'a>(&self, base_ref: &'a mut T, field_name: &'static str) -> Option<DynMut<'a, U>> {
        let (field_type_index, field_offset_bytes, field_size_bytes) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *mut T as *mut u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts_mut::<[u8]>(field_raw_ptr, field_size_bytes);
        Some(DynMut{opaque_value: unsafe { field_ptr.as_mut_unchecked::<'a>() }, type_index: field_type_index, type_universe_phantom_data: PhantomData::default()})
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeEnumConstant<T : ?Sized + StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_has_constant: AtomicBool,
    constant_value: AtomicU64,
    _phantom_enum_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
unsafe impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeEnumConstant<T, U> {}
impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> CachedThreadSafeEnumConstant<T, U> {
    /// Returns the value of the enum constant with the given name
    pub fn get_enum_constant_value(&self, constant_name: &'static str) -> Option<u64> {
        // If there is no value cached, we have to calculate the value here and then release the has_value_cached to make the results visible to other threads
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();

            // We want relaxed ordering here since they will be ordered by has_value_cached anyway
            if let Some(constant_value) = U::type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(U::type_graph(), type_index, constant_name) {
                self.result_has_constant.store(true, Ordering::Relaxed);
                self.constant_value.store(constant_value, Ordering::Relaxed);
            } else {
                self.result_has_constant.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        if self.result_has_constant.load(Ordering::Relaxed) {
            Some(self.constant_value.load(Ordering::Relaxed))
        } else { None }
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeCheckFunctionExists<T : ?Sized + StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_function_exists: AtomicBool,
    _phantom_udt_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
unsafe impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeCheckFunctionExists<T, U> {}
impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> CachedThreadSafeCheckFunctionExists<T, U> {
    /// Returns true if virtual function with the given name exists on the UDT in question
    pub fn does_virtual_function_exist(&self, function_name: &'static str) -> bool {
        // If there is no value cached, we have to calculate the value here and then release the has_value_cached to make the results visible to other threads
        if !self.has_value_cached.load(Ordering::Acquire) {
            let readable_type_graph = U::type_graph().read().unwrap();
            let type_index = readable_type_graph.base_type_index(T::store_type_descriptor_to_universe::<U>());

            let result_function_exists = if let Type::UDT(user_defined_type) = readable_type_graph.type_by_index(type_index) {
                user_defined_type.find_map_member_layout(type_index, function_name, &|context| {
                    if let UserDefinedTypeMember::VirtualFunction(_) = &context.owner_udt.members[context.member_index] { Some(()) } else { None }
                }, readable_type_graph.deref(), &mut U::type_layout_cache().lock().unwrap().layout_cache).unwrap().is_some()
            } else { false };
            self.result_function_exists.store(result_function_exists, Ordering::Relaxed);
            self.has_value_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        self.result_function_exists.load(Ordering::Relaxed)
    }
}

pub(crate) struct CachedFunctionDescriptorData {
    pub(crate) function_name: String,
    pub(crate) function_signature: FunctionSignature,
    pub(crate) function_location: ResolvedUDTVirtualFunctionLocation,
}
pub(crate) type FunctionCallThunkPrototype = unsafe extern "C" fn(*mut u8, *mut u8, *const *mut u8) -> *mut u8;

struct CachedFunctionCallThunkData {
    call_thunk: FunctionCallThunkPrototype,
    // Not actually dead, needed to keep weak pointers alive
    #[allow(dead_code)]
    chunk_reference: CodeChunkReference,
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeMethodCallDescriptor<T : ?Sized + StaticTypeTag, U : TypeUniverse> {
    has_function_data_cached: AtomicBool,
    function_data: AtomicPtr<CachedFunctionDescriptorData>,
    has_validated_parameter_types: AtomicBool,
    call_thunk_data: AtomicPtr<CachedFunctionCallThunkData>,
    has_call_thunk_generated: AtomicBool,
    _phantom_udt_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> Drop for CachedThreadSafeMethodCallDescriptor<T, U> {
    fn drop(&mut self) {
        let function_data_ptr = self.function_data.load(Ordering::Acquire);
        if function_data_ptr != null_mut() {
            drop(unsafe { Box::from_raw(function_data_ptr) });
        }
        let call_thunk_data_ptr = self.call_thunk_data.load(Ordering::Acquire);
        if call_thunk_data_ptr != null_mut() {
            drop(unsafe { Box::from_raw(call_thunk_data_ptr) });
        }
    }
}
unsafe impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeMethodCallDescriptor<T, U> {}
impl<T : ?Sized + StaticTypeTag, U : TypeUniverse> CachedThreadSafeMethodCallDescriptor<T, U> {
    fn get_cached_function_data(&self, function_name: &'static str) -> &CachedFunctionDescriptorData {
        if !self.has_function_data_cached.load(Ordering::Acquire) {
            let readable_type_graph = U::type_graph().read().unwrap();
            let type_index = readable_type_graph.base_type_index(T::store_type_descriptor_to_universe::<U>());

            let result_function_data = if let Type::UDT(user_defined_type) = readable_type_graph.type_by_index(type_index) {
                user_defined_type.find_map_member_layout(type_index, function_name, &|context| {
                    if let UserDefinedTypeMember::VirtualFunction(virtual_function_decl) = &context.owner_udt.members[context.member_index] {
                        let complete_function_name = if let Some(udt_name) = &user_defined_type.name {
                            format!("{}::{}", udt_name.replace('$', "::"), function_name)
                        } else { format!("<unnamed-udt>::{}", function_name) };
                        let function_signature = virtual_function_decl.function_signature();
                        let function_location = context.owner_layout.virtual_function_lookup.get(&function_signature).unwrap().clone();

                        Some(CachedFunctionDescriptorData{function_name: complete_function_name, function_signature, function_location})
                    } else { None }
                }, readable_type_graph.deref(), &mut U::type_layout_cache().lock().unwrap().layout_cache).unwrap()
            } else { None }.unwrap_or_else(|| panic!("Virtual function named {} does not exist on owner UDT", function_name));

            // LEAK: This can be leaked when multiple threads attempt to concurrently cache function data for the same function. However, since this class is global data,
            // and exists for the lifetime of the module, it is fine in this case
            self.function_data.store(Box::into_raw(Box::new(result_function_data)), Ordering::Relaxed);
            self.has_function_data_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        let function_data_ptr = self.function_data.load(Ordering::Relaxed);
        unsafe { function_data_ptr.as_ref() }.unwrap()
    }
    /// Returns true if parameter types have been validated for this function (only used to avoid excessive validation on fully prototyped functions)
    pub fn has_validated_parameter_types(&self) -> bool {
        self.has_validated_parameter_types.load(Ordering::Acquire)
    }
    /// Marks function parameter types as validated, so that has_validated_parameter_types returns true afterward
    pub fn mark_parameter_types_validated(&self) {
        self.has_validated_parameter_types.store(true, Ordering::Release);
    }
    /// Validates that provided parameter types match the function signature
    pub fn validate_parameter_types(&self, function_name: &'static str, prototyped_return_value_type: Option<usize>, mut parameter_types: impl Iterator<Item = usize>) {
        let cached_function_data = self.get_cached_function_data(function_name);

        // Note that these checks are extremely strict as we expect generated types to match function signature types exactly
        if let Some(return_value_type) = prototyped_return_value_type {
            let this_adjust = U::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(U::type_graph(), cached_function_data.function_signature.return_value_type_index, return_value_type);
            assert_eq!(this_adjust, Some(0), "Function {} return type mismatch: Expected Type {}, got Type {}",
                       function_name, Type::type_string(cached_function_data.function_signature.return_value_type_index, U::type_graph().read().unwrap().deref()),
                       Type::type_string(return_value_type, U::type_graph().read().unwrap().deref()));
        }

        let mut current_num_parameter_types = 0;
        for expected_parameter_type in &cached_function_data.function_signature.parameter_type_indices {
            let actual_parameter_type = parameter_types.next().unwrap_or_else(|| panic!("Function {} parameter count mismatch: Expected {}, got {}",
                function_name, cached_function_data.function_signature.parameter_type_indices.len(), current_num_parameter_types));
            current_num_parameter_types += 1;

            let this_adjust = U::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(U::type_graph(), *expected_parameter_type, actual_parameter_type);
            assert_eq!(this_adjust, Some(0), "Function {} parameter type mismatch for parameter #{}: Expected Type {}, got Type {}",
                       function_name, current_num_parameter_types, Type::type_string(*expected_parameter_type,
                       U::type_graph().read().unwrap().deref()), Type::type_string(actual_parameter_type, U::type_graph().read().unwrap().deref()));
        }

        let extra_parameter_count = parameter_types.count();
        if extra_parameter_count != 0 {
            current_num_parameter_types += extra_parameter_count;
            panic!("Function {} parameter count mismatch: Expected {}, got {}", function_name, cached_function_data.function_signature.parameter_type_indices.len(), current_num_parameter_types)
        }
    }
    /// Returns type index of the function return value type, or None if function returns void
    pub fn get_non_void_return_value_type(&self, function_name: &'static str) -> Option<usize> {
        let cached_function_data = self.get_cached_function_data(function_name);
        let return_type_index = cached_function_data.function_signature.return_value_type_index;
        let result_type_definition = U::type_graph().read().unwrap().type_by_index(return_type_index).clone();
        if result_type_definition != Type::Primitive(PrimitiveType::Void) { Some(return_type_index) } else { None }
    }
    /// Returns true if call thunk has been generated already
    pub fn has_prepared_call_thunk(&self) -> bool {
        self.has_call_thunk_generated.load(Ordering::Acquire)
    }
    /// Returns call thunk that was previously generated. Will panic if thunk is not generated
    pub fn get_call_thunk(&self) -> FunctionCallThunkPrototype {
        let call_thunk_data_ptr = self.call_thunk_data.load(Ordering::Acquire);
        unsafe { call_thunk_data_ptr.as_ref() }.unwrap().call_thunk
    }
    /// Prepares the virtual function call thunk to be available
    pub fn prepare_virtual_function_call_thunk(&self, function_name: &'static str, write_return_value_to_return_value_storage: bool, by_value_parameter_passed_as_pointer: &[bool]) {
        if !self.has_call_thunk_generated.load(Ordering::Acquire) {
            let cached_function_data = self.get_cached_function_data(function_name);
            let call_thunk_reference = generate_virtual_function_call_thunk::<U>(cached_function_data, write_return_value_to_return_value_storage, by_value_parameter_passed_as_pointer).unwrap();

            let call_thunk_data = Box::new(CachedFunctionCallThunkData{
                call_thunk: unsafe { mem::transmute::<*const u8, FunctionCallThunkPrototype>(call_thunk_reference.text_start_addr) },
                chunk_reference: call_thunk_reference,
            });
            self.call_thunk_data.store(Box::into_raw(call_thunk_data), Ordering::Release);
            self.has_call_thunk_generated.store(true, Ordering::Release);
        }
    }
}
