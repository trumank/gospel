use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::rc::{Rc};
use anyhow::{anyhow, bail};
use strum_macros::Display;
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::GospelContainer;
use crate::gospel_type::{GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelTargetArch, GospelTargetEnv, GospelTargetOS, GospelFunctionDefinition, GospelObjectIndex, GospelValueType};
use crate::writer::{GospelSourceObjectReference, GospelSourceStaticValue};
use std::str::FromStr;
use serde::{Deserialize, Serialize, Serializer};
use serde::ser::SerializeStruct;
use crate::reflection::{GospelContainerReflector, GospelModuleReflector};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GospelVMStackFrame {
    pub module_name: String,
    pub function_name: String,
    pub source_file_name: Option<String>,
    pub source_line_number: Option<usize>,
}
impl Display for GospelVMStackFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::{}", self.module_name.as_str(), self.function_name.as_str())?;
        if let Some(source_file_name) = &self.source_file_name {
            write!(f, " [{}:{}]", source_file_name.as_str(), self.source_line_number.unwrap_or(0))?;
        }
        Ok({})
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GospelVMError {
    pub message: String,
    pub call_stack: Vec<GospelVMStackFrame>,
}
impl Display for GospelVMError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.message.as_str())?;
        writeln!(f)?;
        for call_stack_frame in &self.call_stack {
            writeln!(f, "{}", call_stack_frame)?;
        }
        Ok({})
    }
}
macro_rules! vm_error {
    ($current_frame:expr, $fmt:expr, $($arg:tt)*) => {
        GospelVMError{message: format!($fmt, $($arg)*), call_stack: $current_frame.map(|x| x.capture_call_stack()).unwrap_or(Vec::new())}
    };
     ($current_frame:expr, $message:expr) => {
        GospelVMError{message: $message.to_string(), call_stack: $current_frame.map(|x| x.capture_call_stack()).unwrap_or(Vec::new())}
    };
}
trait WithVMFrameContext<T> {
    fn with_frame_context(self, current_frame: Option<&GospelVMExecutionState>) -> T;
}
impl<T, S, E : WithVMFrameContext<S>> WithVMFrameContext<Result<T, S>> for Result<T, E> {
    fn with_frame_context(self, current_frame: Option<&GospelVMExecutionState>) -> Result<T, S> {
        self.map_err(|x| x.with_frame_context(current_frame))
    }
}
impl WithVMFrameContext<GospelVMError> for anyhow::Error {
    fn with_frame_context(self, current_frame: Option<&GospelVMExecutionState>) -> GospelVMError {
        vm_error!(current_frame, self.to_string())
    }
}

type GospelVMResult<T> = Result<T, GospelVMError>;
macro_rules! vm_bail {
    ($current_frame:expr, $fmt:expr, $($arg:tt)*) => {
        return GospelVMResult::Err(vm_error!($current_frame, $fmt, $($arg)*));
    };
     ($current_frame:expr, $message:expr) => {
         return GospelVMResult::Err(vm_error!($current_frame, $message));
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GospelBaseClassLayout {
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GospelBitfieldLocation {
    bitfield_bit_offset: usize,
    bitfield_bit_width: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GospelMemberLayout {
    pub name: String,
    pub offset: usize,
    /// If this is a statically sized array, size of the array
    pub array_size: Option<usize>,
    /// If this is a bitfield, this is a location of the bitfield data in the member at the given offset
    pub bitfield_location: Option<GospelBitfieldLocation>,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

/// Represents a fully resolved layout of a particular type
/// This exposes information such as the size of the type, its alignment, unaligned size,
/// and offsets, sizes and full type layouts of its members
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct GospelTypeLayout {
    pub name: String,
    pub alignment: usize,
    pub unaligned_size: usize,
    pub size: usize,
    pub base_classes: Vec<GospelBaseClassLayout>,
    pub members: Vec<GospelMemberLayout>,
    pub pointee_type: Option<Box<GospelTypeLayout>>,
    #[serde(skip_deserializing)]
    pub metadata: Option<GospelVMStruct>,
}
impl GospelTypeLayout {
    /// Creates a new type layout opaque to the VM. Additional members can be added manually if some transparency of the type layout is desired
    pub fn create_opaque(name: String, alignment: usize, size: usize) -> GospelTypeLayout {
        GospelTypeLayout{
            name, alignment, size,
            unaligned_size: size,
            ..GospelTypeLayout::default()
        }
    }
    // Note that returned base offset is absolute, not relative to the parent offset
    pub fn get_base_offset(&self, base: &Self) -> Option<usize> {
        if self.eq(base) {
            return Some(0) // no offset, this is the base
        }
        for base_class in &self.base_classes {
            if let Some(offset_from_base) = base_class.layout.get_base_offset(base) {
                return Some(base_class.offset + offset_from_base) // indirect base, add offset of our direct base to the given value
            }
        }
        None // this type is not based on the type provided
    }
    // Note that returned member offset is absolute, not relative to the parent offset
    pub fn find_named_member(&self, name: &str) -> Option<GospelMemberLayout> {
        for member in &self.members {
            if member.name == name {
                return Some(member.clone()) // this is a direct member of a type
            }
        }
        for base_class in &self.base_classes {
            if let Some(base_member) = base_class.layout.find_named_member(name) {
                return Some(GospelMemberLayout{
                    name: base_member.name,
                    offset: base_class.offset + base_member.offset,
                    array_size: base_member.array_size,
                    bitfield_location: base_member.bitfield_location,
                    actual_size: base_member.actual_size,
                    layout: base_member.layout,
                }) // indirect member, add offset of our direct base to the given offset
            }
        }
        None // member with the name does not exist in this type
    }
}

/// Target triplet defines the target which the type layouts are being calculated for
/// This includes the operating system, the processor architecture, and environment (ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, Clone, Copy)]
pub struct GospelVMTargetTriplet {
    pub arch: GospelTargetArch,
    pub sys: GospelTargetOS,
    pub env: GospelTargetEnv,
}
impl GospelVMTargetTriplet {
    /// Returns the address size for the provided target triplet
    pub fn address_size(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    fn uses_aligned_base_class_size(&self) -> bool {
        self.env == GospelTargetEnv::MSVC // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
    /// Resolves a value of the platform config property
    pub fn resolve_platform_config_property(&self, property: GospelPlatformConfigProperty) -> i32 {
        match property {
            GospelPlatformConfigProperty::TargetArch => { self.arch as i32 }
            GospelPlatformConfigProperty::TargetOS => { self.sys as i32 }
            GospelPlatformConfigProperty::TargetEnv => { self.env as i32 }
            GospelPlatformConfigProperty::AddressSize => { self.address_size() as i32 }
        }
    }
    /// Returns the target that the current executable has been compiled for
    pub fn current_target() -> Option<GospelVMTargetTriplet> {
        let current_arch = GospelTargetArch::current_arch();
        let current_os = GospelTargetOS::current_os();
        let default_env = current_os.as_ref().and_then(|x| x.default_env());

        if current_arch.is_none() || current_os.is_none() || default_env.is_none() {
            None
        } else { Some(GospelVMTargetTriplet{
            arch: current_arch.unwrap(),
            sys: current_os.unwrap(),
            env: default_env.unwrap(),
        }) }
    }
    pub fn parse(triplet_str: &str) -> anyhow::Result<GospelVMTargetTriplet> {
        let splits: Vec<&str> = triplet_str.split('-').collect();
        if splits.len() <= 2 {
            bail!("Target triplet string too short, need at least 2 parts (<arch>-<os>)");
        }
        if splits.len() > 3 {
            bail!("Target triplet string too long, should consist of at most 3 parts (<arch>-<os>-<env>)");
        }
        let arch = GospelTargetArch::from_str(splits[0])
            .map_err(|x| anyhow!("Failed to parse arch: {}", x.to_string()))?;
        let sys = GospelTargetOS::from_str(splits[1])
            .map_err(|x| anyhow!("Failed to parse OS: {}", x.to_string()))?;
        let env = if splits.len() >= 3 {
            GospelTargetEnv::from_str(splits[2])
                .map_err(|x| anyhow!("Failed to parse env: {}", x.to_string()))?
        } else {
            sys.default_env().ok_or_else(|| anyhow!("Default env for OS not available please specify env manually (<arch>-<os>-<env>)"))?
        };
        Ok(GospelVMTargetTriplet{arch, sys, env})
    }
}

/// Represents reference to a function located in a particular container
#[derive(Clone)]
pub struct GospelVMClosure {
    container: Rc<GospelVMContainer>,
    function_index: u32,
    arguments: Vec<GospelVMValue>,
}
impl Debug for GospelVMClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
impl PartialEq for GospelVMClosure {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.container, &other.container) &&
            self.function_index == other.function_index &&
            self.arguments == other.arguments
    }
}
impl Eq for GospelVMClosure {}
impl Display for GospelVMClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let container_name = self.container.container_name().unwrap_or("<unknown>");
        let function_name = self.function_name().unwrap_or("<unnamed>");
        write!(f, "{}:{}", container_name, function_name)
    }
}
impl Serialize for GospelVMClosure {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        let mut s = serializer.serialize_struct("GospelVMFunctionPointer", 2)?;
        s.serialize_field("module", &self.source_container().container_name().unwrap_or("<unknown>"))?;
        s.serialize_field("function", &self.function_name().unwrap_or("<unnamed>"))?;
        s.end()
    }
}
impl GospelVMClosure {
    /// Returns the type container which defines this type
    pub fn source_container(&self) -> Rc<GospelVMContainer> {
        self.container.clone()
    }
    /// Returns the name of the function this closure is created from
    pub fn function_name(&self) -> Option<&str> {
        if (self.function_index as usize) < self.container.container.functions.len() {
            self.container.container.strings.get(self.container.container.functions[self.function_index as usize].name).ok()
        } else { None }
    }
    /// Attempts to execute this closure and returns the result
    pub fn execute(&self, args: Vec<GospelVMValue>) -> GospelVMResult<GospelVMValue> {
        self.execute_internal(args, None)
    }
    fn execute_internal(&self, args: Vec<GospelVMValue>, previous_frame: Option<&GospelVMExecutionState>) -> GospelVMResult<GospelVMValue> {
        if self.arguments.is_empty() {
            self.container.execute_function_internal(self.function_index, &args, previous_frame)
        } else if args.is_empty() {
            self.container.execute_function_internal(self.function_index, &self.arguments, previous_frame)
        } else {
            let mut concat_args = self.arguments.clone();
            concat_args.extend(args.into_iter());
            self.container.execute_function_internal(self.function_index, &concat_args, previous_frame)
        }
    }
}

/// Represents a type of the struct in the VM
#[derive(Debug)]
pub struct GospelVMStructTemplate {
    name: Option<String>,
    fields: Vec<(GospelValueType, String)>,
    property_index_lookup: HashMap<String, usize>,
    source_container_name: String,
}
impl GospelVMStructTemplate {
    /// Returns the name of the struct this template represents
    pub fn struct_name(&self) -> Option<&str> {
        self.name.as_ref().map(|x| x.as_str())
    }
    /// Returns the type container which defines this struct type
    pub fn source_container_name(&self) -> &str {
        self.source_container_name.as_str()
    }
    /// Returns the index of the property by name
    pub fn find_named_property_index(&self, name: &str) -> Option<usize> {
        self.property_index_lookup.get(name).cloned()
    }
    /// Allocates a new struct instance using this template
    pub fn allocate_struct(self: &Rc<Self>) -> GospelVMStruct {
        let fields: Vec<Option<GospelVMValue>> = vec![None; self.fields.len()];
        GospelVMStruct{ fields, template: self.clone() }
    }
}

/// Represents an instance of a structure in the VM
#[derive(Debug, Clone)]
pub struct GospelVMStruct {
    fields: Vec<Option<GospelVMValue>>,
    template: Rc<GospelVMStructTemplate>,
}
impl PartialEq for GospelVMStruct {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.template, &other.template) && self.fields == other.fields
    }
}
impl Eq for GospelVMStruct {}
impl Display for GospelVMStruct {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let module_name = self.template.source_container_name();
        let struct_name = self.template.struct_name().unwrap_or("<unnamed>");

        let named_field_values: Vec<String> = self.fields.iter().enumerate()
            .filter_map(|(index, maybe_value)|
                maybe_value.as_ref().map(|x| (index, x.clone())))
            .map(|(index, value)| (self.template.fields[index].1.as_str(), value))
            .map(|(name, value)| format!("{} = {}", name, value.to_string()))
            .collect();
        write!(f, "{}:{}[{}]", module_name, struct_name, named_field_values.join(", "))
    }
}
impl Serialize for GospelVMStruct {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        let module_name = self.template.source_container_name();
        let struct_name = self.template.struct_name().unwrap_or("<unnamed>");

        let named_field_values: HashMap<String, GospelVMValue> = self.fields.iter().enumerate()
            .filter_map(|(index, maybe_value)|
                maybe_value.as_ref().map(|x| (index, x.clone())))
            .map(|(index, value)| (self.template.fields[index].1.clone(), value))
            .collect();

        let mut s = serializer.serialize_struct("GospelVMStruct", 3)?;
        s.serialize_field("module", &module_name)?;
        s.serialize_field("struct", &struct_name)?;
        s.serialize_field("fields", &named_field_values)?;
        s.end()
    }
}
impl GospelVMStruct {
    /// Returns the template from which this struct instance has been created
    pub fn struct_template(&self) -> Rc<GospelVMStructTemplate> {
        self.template.clone()
    }
    /// Attempts to read the value of the property at given index
    pub fn get_raw_property(&self, index: usize) -> anyhow::Result<Option<&GospelVMValue>> {
        if index >= self.fields.len() {
            bail!("Struct property index #{} out of bounds (number of fields: {})", index, self.fields.len());
        }
        Ok(self.fields[index].as_ref())
    }
    /// Attempts to borrow the value of the property at given index
    pub fn take_raw_property(mut self, index: usize) -> anyhow::Result<Option<GospelVMValue>> {
        if index >= self.fields.len() {
            bail!("Struct property index #{} out of bounds (number of fields: {})", index, self.fields.len());
        }
        Ok(std::mem::take(&mut self.fields[index]))
    }
    pub fn set_raw_property(&mut self, index: usize, value: Option<GospelVMValue>) -> anyhow::Result<()> {
        if index >= self.fields.len() {
            bail!("Struct property index #{} out of bounds (number of fields: {})", index, self.fields.len());
        }
        if value.is_some() && self.template.fields[index].0 != value.as_ref().unwrap().value_type() {
            bail!("Incompatible property type for field #{} of type {}", index, self.template.fields[index].0.to_string());
        }
        self.fields[index] = value;
        Ok({})
    }
    /// Attempts to read a value of a struct property by name. Returns an error if property with that name does not exist, an empty option if it is not set, or a value otherwise
    pub fn get_named_property(&self, name: &str) -> anyhow::Result<Option<&GospelVMValue>> {
        let property_index = self.template.find_named_property_index( name)
            .ok_or_else(|| anyhow!("Struct does not have a property with name '{}'", name))?;
        self.get_raw_property(property_index)
    }
    /// Attempts to borrow a value of a struct property by name. Returns an error if property with that name does not exist, an empty option if it is not set, or a value otherwise
    pub fn take_named_property(self, name: &str) -> anyhow::Result<Option<GospelVMValue>> {
        let property_index = self.template.find_named_property_index( name)
            .ok_or_else(|| anyhow!("Struct does not have a property with name '{}'", name))?;
        self.take_raw_property(property_index)
    }
    /// Attempts to write a value of a struct property by name. Returns an error if property with that name does not exist
    pub fn set_named_property(&mut self, name: &str, value: Option<GospelVMValue>) -> anyhow::Result<()> {
        let property_index = self.template.find_named_property_index(name)
            .ok_or_else(|| anyhow!("Struct does not have a property with name '{}'", name))?;
        self.set_raw_property(property_index, value)
    }
}

/// VM Value represents a value that VM bytecode can read and write
/// Currently supported value types are integers, function pointers and type layouts
/// Function pointers can be called to yield their return value
/// Values can be compared for equality, but values of certain types might never be equivalent (for example, unnamed type layouts are never equivalent, even to themselves)
#[derive(Debug, Clone, PartialEq, Eq, Display, Serialize)]
pub enum GospelVMValue {
    #[strum(to_string = "Integer({0})")]
    Integer(i32), // signed 32-bit integer value
    #[strum(to_string = "Closure({0})")]
    Closure(GospelVMClosure), // pointer to a function with some number (or no) arguments captured with it
    #[strum(to_string = "TypeLayout({0:#?})")]
    TypeLayout(GospelTypeLayout), // pre-computed type layout
    #[strum(to_string = "Array({0:#?})")]
    Array(Vec<GospelVMValue>), // array of values
    #[strum(to_string = "Struct({0})")]
    Struct(GospelVMStruct), // user defined struct
}
impl GospelVMValue {
    pub fn value_type(&self) -> GospelValueType {
        match self {
            GospelVMValue::Integer(_) => { GospelValueType::Integer }
            GospelVMValue::Closure(_) => { GospelValueType::Closure }
            GospelVMValue::TypeLayout(_) => { GospelValueType::TypeLayout }
            GospelVMValue::Array(_) => { GospelValueType::Array }
            GospelVMValue::Struct(_) => { GospelValueType::Struct }
        }
    }
}

#[derive(Debug)]
struct GospelGlobalStorage {
    name: String,
    initial_value: RefCell<Option<i32>>,
    current_value: RefCell<Option<i32>>,
}

#[derive(Debug)]
struct GospelVMExecutionState<'a> {
    owner_container: &'a Rc<GospelVMContainer>,
    function_definition: &'a GospelFunctionDefinition,
    slots: Vec<Option<GospelVMValue>>,
    referenced_strings: Vec<String>,
    referenced_structs: Vec<Rc<GospelVMStructTemplate>>,
    stack: Vec<GospelVMValue>,
    current_instruction_index: usize,
    current_loop_jump_count: usize,
    previous_frame: Option<&'a GospelVMExecutionState<'a>>,
    recursion_counter: usize,
    max_stack_size: usize,
    max_loop_jumps: usize,
    max_recursion_depth: usize,
}
impl GospelVMExecutionState<'_> {
    fn align_value(value: usize, align: usize) -> usize {
        let reminder = if align == 0 { 0 } else { value % align };
        if reminder == 0 { value } else { value + (align - reminder) }
    }
    fn push_stack_check_overflow(&mut self, value: GospelVMValue) -> GospelVMResult<()> {
        if self.stack.len() > self.max_stack_size {
            vm_bail!(Some(self), "Stack overflow");
        }
        self.stack.push(value);
        Ok({})
    }
    fn pop_stack_check_underflow(&mut self) -> GospelVMResult<GospelVMValue> {
        if self.stack.len() == 0 {
            vm_bail!(Some(self), "Stack underflow");
        }
        Ok(self.stack.pop().unwrap())
    }
    fn jump_control_flow_checked(&mut self, target_index: usize) -> GospelVMResult<()> {
        if target_index >= self.function_definition.code.len() {
            vm_bail!(Some(self), "Invalid control flow jump to instruction index #{} out of bounds (number of instructions: {})", target_index, self.function_definition.code.len());
        }
        // If we are jumping back, this is a loop, and we need to check the loop limit
        if target_index < self.current_instruction_index {
            self.current_loop_jump_count += 1;
            if self.current_loop_jump_count > self.max_loop_jumps {
                vm_bail!(Some(self), "Loop limit reached");
            }
        }
        self.current_instruction_index = target_index;
        Ok({})
    }
    fn read_slot_value_checked(&mut self, index: usize) -> GospelVMResult<GospelVMValue> {
        if index >= self.slots.len() {
            vm_bail!(Some(self), "Invalid slot index #{} out of bounds (number of slots: {})", index, self.slots.len());
        }
        self.slots[index].clone().ok_or_else(|| vm_error!(Some(self), "Invalid read of uninitialized data from slot at index #{}", index))
    }
    fn borrow_slot_value_checked(&mut self, index: usize) -> GospelVMResult<GospelVMValue> {
        if index >= self.slots.len() {
            vm_bail!(Some(self), "Invalid slot index #{} out of bounds (number of slots: {})", index, self.slots.len());
        }
        self.slots[index].take().ok_or_else(|| vm_error!(Some(self), "Invalid read of uninitialized data from slot at index #{}", index))
    }
    fn write_slot_value_checked(&mut self, index: usize, value: GospelVMValue) -> GospelVMResult<()> {
        if index >= self.slots.len() {
            vm_bail!(Some(self), "Invalid slot index #{} out of bounds (number of slots: {})", index, self.slots.len());
        }
        if self.function_definition.slots[index].value_type != value.value_type() {
            vm_bail!(Some(self), "Invalid write of incompatible value type to slot at index #{}", index);
        }
        self.slots[index] = Some(value);
        Ok({})
    }
    fn immediate_value_checked(&self, inst: &GospelInstruction, index: usize) -> GospelVMResult<u32> {
        inst.immediate_operand_at(index).ok_or_else(|| vm_error!(Some(self), "Invalid instruction encoding: Missing immediate operand #{}", index))
    }
    fn copy_referenced_string_checked(&self, index: usize) -> GospelVMResult<String> {
        if index >= self.referenced_strings.len() {
            vm_bail!(Some(self), "Invalid referenced string index #{} out of bounds (number of referenced strings: {})", index, self.referenced_strings.len());
        }
        Ok(self.referenced_strings[index].clone())
    }
    fn get_referenced_struct_checked(&self, index: usize) -> GospelVMResult<Rc<GospelVMStructTemplate>> {
        if index >= self.referenced_structs.len() {
            vm_bail!(Some(self), "Invalid referenced struct index #{} out of bounds (number of referenced structs: {})", index, self.referenced_structs.len());
        }
        Ok(self.referenced_structs[index].clone())
    }
    fn unwrap_value_as_int_checked(&self, value: GospelVMValue) -> GospelVMResult<i32> {
        match value {
            GospelVMValue::Integer(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected integer value, got value of different type"))
        }
    }
    fn unwrap_value_as_function_pointer_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelVMClosure> {
        match value {
            GospelVMValue::Closure(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected function pointer, got value of different type"))
        }
    }
    fn validate_type_layout_complete(&self, value: &GospelVMValue) -> GospelVMResult<()> {
        if let GospelVMValue::TypeLayout(type_layout) = value {
            if type_layout.size == 0 {
                vm_bail!(Some(self), "Expected a complete type layout value, but got an incomplete type layout. Non-finalized type layouts cannot be read");
            }
        }
        Ok({})
    }
    fn validate_struct_instance_template(&self, instance: &GospelVMStruct, template: &Rc<GospelVMStructTemplate>) -> GospelVMResult<()> {
        if !Rc::ptr_eq(&instance.template, template) {
            vm_bail!(Some(self), "Expected a struct value of type {}, got struct value of type {}",
                template.struct_name().unwrap_or("<unnamed>"), instance.template.struct_name().unwrap_or("<unnamed>"));
        }
        Ok({})
    }
    fn unwrap_value_as_complete_type_layout_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelTypeLayout> {
        match value {
            GospelVMValue::TypeLayout(unwrapped) => {
                if unwrapped.size == 0 {
                    vm_bail!(Some(self), "Expected a complete type layout value, but got an incomplete type layout. Non-finalized type layouts cannot be read");
                }
                Ok(unwrapped)
            }
            _ => Err(vm_error!(Some(self), "Expected type layout value, got value of a different type"))
        }
    }
    fn unwrap_value_as_partial_type_layout_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelTypeLayout> {
        match value {
            GospelVMValue::TypeLayout(unwrapped) => {
                if unwrapped.size != 0 {
                    vm_bail!(Some(self), "Expected a partial type layout, but got a complete type layout. Finalized type layouts cannot be written");
                }
                Ok(unwrapped)
            }
            _ => Err(vm_error!(Some(self), "Expected type layout value, got value of a different type"))
        }
    }
    fn unwrap_value_as_array_checked(&self, value: GospelVMValue) -> GospelVMResult<Vec<GospelVMValue>> {
        match value {
            GospelVMValue::Array(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected array value, got value of different type"))
        }
    }
    fn unwrap_value_as_struct_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelVMStruct> {
        match value {
            GospelVMValue::Struct(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected struct value, got value of different type"))
        }
    }
    fn do_bitwise_op<F: Fn(u32, u32) -> u32>(&mut self, op: F) -> GospelVMResult<()> {
        let stack_value_b = self.pop_stack_check_underflow().and_then(|x| self.unwrap_value_as_int_checked(x))? as u32;
        let stack_value_a = self.pop_stack_check_underflow().and_then(|x| self.unwrap_value_as_int_checked(x))? as u32;
        let result = op(stack_value_a, stack_value_b) as i32;
        self.push_stack_check_overflow(GospelVMValue::Integer(result))
    }
    fn do_arithmetic_op_checked<F: Fn(&Self, i32, i32) -> GospelVMResult<i32>>(&mut self, op: F) -> GospelVMResult<()> {
        let stack_value_b = self.pop_stack_check_underflow().and_then(|x| self.unwrap_value_as_int_checked(x))?;
        let stack_value_a = self.pop_stack_check_underflow().and_then(|x| self.unwrap_value_as_int_checked(x))?;
        let result = op(&self, stack_value_a, stack_value_b)?;
        self.push_stack_check_overflow(GospelVMValue::Integer(result))
    }
    fn do_member_access_op_checked<F: Fn(GospelMemberLayout) -> GospelVMValue>(&mut self, member_name_index: usize, op: F) -> GospelVMResult<()> {
        let member_name = self.copy_referenced_string_checked(member_name_index)?;
        let type_layout = self.pop_stack_check_underflow().and_then(|x| self.unwrap_value_as_complete_type_layout_checked(x))?;

        let result_member = type_layout.find_named_member(member_name.as_str()).ok_or_else(|| {
            vm_error!(Some(self), "Failed to find member named {} inside type {}", member_name.clone(), type_layout.name.clone())
        })?;
        op(result_member);
        Ok({})
    }
    fn current_stack_frame(&self) -> GospelVMStackFrame {
        let module_name = self.owner_container.container_name().unwrap_or("<unknown>").to_string();
        let function_name = self.owner_container.container.strings.get(self.function_definition.name).map(|x| x.to_string()).unwrap_or(String::from("<unknown>"));

        let (source_file_name, source_line_number) = if let Some(debug_data) = &self.function_definition.debug_data {
            let source_file_name = self.owner_container.container.strings.get(debug_data.source_file_name).unwrap_or("<unknown>").to_string();
            let actual_inst_index = self.current_instruction_index - 1;
            let source_line_number = if debug_data.instruction_line_numbers.len() > actual_inst_index && debug_data.instruction_line_numbers[actual_inst_index] != -1 {
                Some(debug_data.instruction_line_numbers[actual_inst_index] as usize)
            } else { None };
            (Some(source_file_name), source_line_number)
        } else { (None, None) };
        GospelVMStackFrame{ module_name, function_name, source_file_name, source_line_number }
    }
    fn capture_call_stack(&self) -> Vec<GospelVMStackFrame> {
        let mut result_call_stack: Vec<GospelVMStackFrame> = Vec::new();
        let mut maybe_current_frame: Option<&GospelVMExecutionState> = Some(self);
        while let Some(current_frame) = maybe_current_frame {
            result_call_stack.push(current_frame.current_stack_frame());
            maybe_current_frame = current_frame.previous_frame;
        }
        result_call_stack
    }
    fn run(state: &mut GospelVMExecutionState) -> GospelVMResult<GospelVMValue> {
        // Main VM loop
        state.current_instruction_index = 0;
        state.current_loop_jump_count = 0;
        while state.current_instruction_index < state.function_definition.code.len() {
            let instruction = &state.function_definition.code[state.current_instruction_index];
            state.current_instruction_index += 1;
            match instruction.opcode() {
                // Basic opcodes
                GospelOpcode::Noop => {}
                GospelOpcode::IntConstant => {
                    let int_value = state.immediate_value_checked(instruction, 0)? as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(int_value))?;
                }
                GospelOpcode::Dup => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    state.push_stack_check_overflow(stack_value.clone())?;
                    state.push_stack_check_overflow(stack_value)?;
                }
                GospelOpcode::Permute => {
                    let stack_value_1 = state.pop_stack_check_underflow()?;
                    let stack_value_2 = state.pop_stack_check_underflow()?;
                    state.push_stack_check_overflow(stack_value_1)?;
                    state.push_stack_check_overflow(stack_value_2)?;
                }
                GospelOpcode::Pop => {
                    state.pop_stack_check_underflow()?;
                }
                GospelOpcode::Equals => {
                    let stack_value_a = state.pop_stack_check_underflow()?;
                    let stack_value_b = state.pop_stack_check_underflow()?;

                    // This is a bit too aggressive, but we do not want incomplete type values to leak any information about their contents until they are finalized
                    state.validate_type_layout_complete(&stack_value_a)?;
                    state.validate_type_layout_complete(&stack_value_b)?;

                    let result = stack_value_a == stack_value_b;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::ReturnValue => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    if stack_value.value_type() != state.function_definition.return_value_type {
                        vm_bail!(Some(&state), "Incompatible return value type");
                    }
                    if !state.stack.is_empty() {
                        vm_bail!(Some(&state), "Stack not empty upon function return");
                    }
                    return Ok(stack_value)
                }
                GospelOpcode::Call => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut function_arguments: Vec<GospelVMValue> = vec![GospelVMValue::Integer(0); number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow()?;
                        function_arguments[number_of_arguments - index - 1] = argument_value;
                    }
                    let closure = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_function_pointer_checked(x))?;
                    if state.recursion_counter >= state.max_recursion_depth {
                        vm_bail!(Some(&state), "Recursion limit reached");
                    }
                    let return_value = closure.execute_internal(function_arguments, Some(&state))?;
                    state.push_stack_check_overflow(return_value)?;
                }
                GospelOpcode::BindClosure => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut closure_arguments: Vec<GospelVMValue> = vec![GospelVMValue::Integer(0); number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow()?;
                        closure_arguments[number_of_arguments - index - 1] = argument_value;
                    }
                    let mut closure = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_function_pointer_checked(x))?;
                    closure.arguments.append(&mut closure_arguments);
                    if closure.arguments.len() >= state.max_stack_size {
                        vm_bail!(Some(&state), "Closure captured argument number limit reached");
                    }
                    state.push_stack_check_overflow(GospelVMValue::Closure(closure))?;
                }
                GospelOpcode::Abort => {
                    let message_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let message = state.copy_referenced_string_checked(message_index)?;
                    vm_bail!(Some(&state), "Aborted: {}", message);
                }
                GospelOpcode::Typeof => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let result = stack_value.value_type() as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                // Logical opcodes
                GospelOpcode::And => { state.do_bitwise_op(|a, b| a & b)?; }
                GospelOpcode::Or => { state.do_bitwise_op(|a, b| a | b)?; }
                GospelOpcode::Xor => { state.do_bitwise_op(|a, b| a ^ b)?; }
                GospelOpcode::Shl => { state.do_bitwise_op(|a, b| a >> b)?; }
                GospelOpcode::Shr => { state.do_bitwise_op(|a, b| a << b)?; }
                GospelOpcode::ReverseBits => {
                    let stack_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as u32;
                    let result = stack_value.reverse_bits() as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::Ez => {
                    let stack_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as u32;
                    let result = if stack_value == 0 { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::Lz => {
                    let stack_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))?;
                    let result = if stack_value < 0 { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::Lez => {
                    let stack_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))?;
                    let result = if stack_value <= 0 { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                // Arithmetic opcodes
                GospelOpcode::Add => { state.do_arithmetic_op_checked(|_, a, b| Ok(a + b))?; }
                GospelOpcode::Sub => { state.do_arithmetic_op_checked(|_, a, b| Ok(a - b))?; }
                GospelOpcode::Mul => { state.do_arithmetic_op_checked(|_, a, b| Ok(a * b))?; }
                GospelOpcode::Div => {
                    state.do_arithmetic_op_checked(|local_state, a, b| {
                        if b == 0 { Err(vm_error!(Some(local_state), "Division by zero")) } else { Ok(a / b) }
                    })?;
                }
                GospelOpcode::Rem => {
                    state.do_arithmetic_op_checked(|local_state, a, b| {
                        if b == 0 { Err(vm_error!(Some(local_state), "Division by zero")) } else { Ok(a % b) }
                    })?;
                }
                GospelOpcode::Neg => {
                    let stack_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))?;
                    let result = -stack_value;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                // Control flow opcodes
                GospelOpcode::Branch => {
                    let target_instruction_index = state.immediate_value_checked(instruction, 0)? as usize;
                    state.jump_control_flow_checked(target_instruction_index)?;
                }
                GospelOpcode::Branchz => {
                    let target_instruction_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let condition_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as u32;
                    if condition_value == 0 {
                        state.jump_control_flow_checked(target_instruction_index)?;
                    }
                }
                // Data storage opcodes
                GospelOpcode::LoadSlot => {
                    let slot_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let current_slot_value = state.read_slot_value_checked(slot_index)?;
                    state.push_stack_check_overflow(current_slot_value)?;
                }
                GospelOpcode::StoreSlot => {
                    let slot_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let new_slot_value = state.pop_stack_check_underflow()?;
                    state.write_slot_value_checked(slot_index, new_slot_value)?;
                }
                GospelOpcode::TakeSlot => {
                    let slot_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let old_slot_value = state.borrow_slot_value_checked(slot_index)?;
                    state.push_stack_check_overflow(old_slot_value)?;
                }
                // Type layout access opcodes
                GospelOpcode::TypeLayoutGetSize => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.size as i32))?;
                }
                GospelOpcode::TypeLayoutGetAlignment => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.alignment as i32))?;
                }
                GospelOpcode::TypeLayoutGetUnalignedSize => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.unaligned_size as i32))?;
                }
                GospelOpcode::TypeLayoutDoesMemberExist => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;

                    let result = type_layout.members.iter().any(|x| x.name == member_name);
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberSize => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::Integer(x.actual_size as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberOffset => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::Integer(x.offset as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberTypeLayout => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::TypeLayout(x.layout))?;
                }
                GospelOpcode::TypeLayoutIsChildOf => {
                    let child_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let parent_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;

                    let result = child_layout.get_base_offset(&parent_layout).is_some();
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::TypeLayoutGetOffsetOfBase => {
                    let child_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let parent_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;

                    let result = child_layout.get_base_offset(&parent_layout)
                        .ok_or_else(|| vm_error!(Some(&state), "Type {} is not a base of type {}", child_layout.name.clone(), parent_layout.name.clone()))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                // Structure opcodes
                GospelOpcode::TypeLayoutAllocate => {
                    let type_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let type_name = state.copy_referenced_string_checked(type_name_index)?;

                    let allocated_layout = GospelTypeLayout{
                        name: type_name,
                        alignment: 1,
                        unaligned_size: 0,
                        size: 0, // size 0 is an implicit marked of a partial type layout
                        ..GospelTypeLayout::default()
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(allocated_layout))?;
                }
                GospelOpcode::TypeLayoutAlign => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let alignment = state.unwrap_value_as_int_checked(stack_value)? as usize;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    if alignment == 0 {
                        vm_bail!(Some(&state), "Invalid alignment of zero (division by zero)");
                    }
                    layout_builder.alignment = max(layout_builder.alignment, alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, alignment);
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutPad => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let padding_bytes = state.unwrap_value_as_int_checked(stack_value)? as usize;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    layout_builder.unaligned_size += padding_bytes;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineBaseClass => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let base_class_layout = state.unwrap_value_as_complete_type_layout_checked(stack_value)?;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    // Make sure the alignment requirement is met for the base class
                    layout_builder.alignment = max(layout_builder.alignment, base_class_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, base_class_layout.alignment);

                    // Actual class size differs depending on ABI used, on MSVC aligned base class size is used, while on GNU/Darwin
                    // unaligned class size is used, saving some space on derived types that are inherited from base classes ending with alignment padding
                    let actual_base_class_size = if state.owner_container.target_triplet.uses_aligned_base_class_size() {
                        base_class_layout.size
                    } else { base_class_layout.unaligned_size };

                    layout_builder.base_classes.push(GospelBaseClassLayout{
                        offset: layout_builder.unaligned_size,
                        actual_size: actual_base_class_size,
                        layout: base_class_layout,
                    });
                    layout_builder.unaligned_size += actual_base_class_size;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineMember => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let stack_value = state.pop_stack_check_underflow()?;
                    let member_layout = state.unwrap_value_as_complete_type_layout_checked(stack_value)?;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    // Make sure the alignment requirement is met for the member
                    layout_builder.alignment = max(layout_builder.alignment, member_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, member_layout.alignment);

                    let actual_size = member_layout.size;
                    layout_builder.members.push(GospelMemberLayout{
                        name: member_name,
                        offset: layout_builder.unaligned_size,
                        array_size: None,
                        bitfield_location: None,
                        actual_size,
                        layout: member_layout,
                    });
                    layout_builder.unaligned_size += actual_size;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineArrayMember => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let array_size = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let member_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    // Make sure the alignment requirement is met for the member
                    layout_builder.alignment = max(layout_builder.alignment, member_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, member_layout.alignment);

                    let actual_size = member_layout.size * array_size;
                    layout_builder.members.push(GospelMemberLayout{
                        name: member_name,
                        offset: layout_builder.unaligned_size,
                        array_size: Some(array_size),
                        bitfield_location: None,
                        actual_size,
                        layout: member_layout,
                    });
                    layout_builder.unaligned_size += actual_size;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineBitfieldMember => {
                    let member_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let bitfield_width = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let member_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    // See if we can fit this bitfield at the offset allocated to the previous member, given that it is of the same type and has enough bits of unallocated storage left
                    if let Some(previous_bitfield_member) = layout_builder.members.last() &&
                        let Some(previous_bitfield_location) = &previous_bitfield_member.bitfield_location &&
                        previous_bitfield_member.layout == member_layout &&
                        let new_bitfield_start_offset = previous_bitfield_location.bitfield_bit_offset + previous_bitfield_location.bitfield_bit_width &&
                        let member_layout_bit_width = previous_bitfield_member.actual_size * 8 &&
                        new_bitfield_start_offset + bitfield_width <= member_layout_bit_width {

                        let new_bitfield_location = GospelBitfieldLocation{
                            bitfield_bit_offset: new_bitfield_start_offset,
                            bitfield_bit_width: bitfield_width,
                        };
                        let new_bitfield_member = GospelMemberLayout{
                            name: member_name,
                            offset: previous_bitfield_member.offset,
                            array_size: None,
                            bitfield_location: Some(new_bitfield_location),
                            actual_size: previous_bitfield_member.actual_size,
                            layout: previous_bitfield_member.layout.clone(),
                        };
                        layout_builder.members.push(new_bitfield_member);
                    } else {
                        // We could not fit this bitfield into the previous member, so we need to allocate storage for it at the end of the struct
                        layout_builder.alignment = max(layout_builder.alignment, member_layout.alignment);
                        layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, member_layout.alignment);

                        let new_bitfield_location = GospelBitfieldLocation{
                            bitfield_bit_offset: 0,
                            bitfield_bit_width: bitfield_width,
                        };
                        let actual_size = member_layout.size;
                        let new_bitfield_member = GospelMemberLayout{
                            name: member_name,
                            offset: layout_builder.unaligned_size,
                            array_size: None,
                            bitfield_location: Some(new_bitfield_location),
                            actual_size,
                            layout: member_layout,
                        };
                        layout_builder.members.push(new_bitfield_member);
                        layout_builder.unaligned_size += actual_size;
                    }
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutFinalize => {
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    // Make sure the size is at least one byte, and calculate the aligned size from unaligned size
                    if layout_builder.unaligned_size == 0 {
                        layout_builder.unaligned_size = 1;
                    }
                    layout_builder.size = Self::align_value(layout_builder.unaligned_size, layout_builder.alignment);
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutSetMetadata => {
                    let metadata_struct = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;
                    let mut layout_builder = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_partial_type_layout_checked(x))?;

                    layout_builder.metadata = Some(metadata_struct);
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutGetMetadata => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let metadata_struct = type_layout.metadata.ok_or_else(|| vm_error!(Some(&state), "Type layout metadata not set on type layout"))?;
                    state.push_stack_check_overflow(GospelVMValue::Struct(metadata_struct))?;
                }
                GospelOpcode::TypeLayoutCreatePointer => {
                    let pointee_type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let pointer_type_layout = GospelTypeLayout{
                        name: format!("{}*", pointee_type_layout.name.as_str()),
                        alignment: state.owner_container.target_triplet.address_size(),
                        unaligned_size: state.owner_container.target_triplet.address_size(),
                        size: state.owner_container.target_triplet.address_size(),
                        base_classes: Vec::new(),
                        members: Vec::new(),
                        pointee_type: Some(Box::new(pointee_type_layout)),
                        metadata: None,
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(pointer_type_layout))?;
                }
                GospelOpcode::TypeLayoutIsPointer => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    let result = if type_layout.pointee_type.is_some() { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeLayoutGetPointerPointeeType => {
                    let type_layout = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_complete_type_layout_checked(x))?;
                    if type_layout.pointee_type.is_none() {
                        vm_bail!(Some(&state), "Attempt to get pointee type from a non-pointer type");
                    }
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(*type_layout.pointee_type.unwrap()))?;
                }
                // Array opcodes
                GospelOpcode::ArrayGetLength => {
                    let array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(array.len() as i32))?;
                }
                GospelOpcode::ArrayGetItem => {
                    let element_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let mut array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;

                    if array.len() <= element_index {
                        vm_bail!(Some(&state), "Array element index #{} out of bounds (number of elements: {})", element_index, array.len());
                    }
                    state.push_stack_check_overflow(std::mem::replace(&mut array[element_index], GospelVMValue::Integer(0)))?;
                }
                GospelOpcode::ArrayAllocate => {
                    let array = GospelVMValue::Array(Vec::new());
                    state.push_stack_check_overflow(array)?;
                }
                GospelOpcode::ArrayReserve => {
                    let reserve_amount = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let mut array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;

                    if array.len() + reserve_amount > i32::MAX as usize {
                        vm_bail!(Some(&state), "Array size exceeds maximum allowed size");
                    }
                    array.reserve(reserve_amount);
                    state.push_stack_check_overflow(GospelVMValue::Array(array))?;
                }
                GospelOpcode::ArrayPushItem => {
                    let new_item = state.pop_stack_check_underflow()?;
                    let mut array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;

                    if array.len() + 1 > i32::MAX as usize {
                        vm_bail!(Some(&state), "Array size exceeds maximum allowed size");
                    }
                    array.push(new_item);
                    state.push_stack_check_overflow(GospelVMValue::Array(array))?;
                }
                GospelOpcode::ArrayInsertItem => {
                    let new_item = state.pop_stack_check_underflow()?;
                    let insert_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let mut array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;

                    if array.len() + 1 > i32::MAX as usize {
                        vm_bail!(Some(&state), "Array size exceeds maximum allowed size");
                    }
                    if array.len() < insert_index {
                        vm_bail!(Some(&state), "Array insert index #{} out of bounds (number of elements: {})", insert_index, array.len());
                    }
                    array.insert(insert_index, new_item);
                    state.push_stack_check_overflow(GospelVMValue::Array(array))?;
                }
                GospelOpcode::ArrayRemoveItem => {
                    let remove_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let mut array = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_array_checked(x))?;

                    if array.len() <= remove_index {
                        vm_bail!(Some(&state), "Array remove index #{} out of bounds (number of elements: {})", remove_index, array.len());
                    }
                    array.remove(remove_index);
                    state.push_stack_check_overflow(GospelVMValue::Array(array))?;
                }
                // Struct opcodes
                GospelOpcode::StructAllocate => {
                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;
                    state.push_stack_check_overflow(GospelVMValue::Struct(struct_template.allocate_struct()))?;
                }
                GospelOpcode::StructGetLocalField => {
                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;

                    let struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;
                    state.validate_struct_instance_template(&struct_value, &struct_template)?;

                    let struct_field_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let field_value = struct_value.take_raw_property(struct_field_index).with_frame_context(Some(&state))?
                        .ok_or_else(|| anyhow!("Field #{} is not set on struct instance", struct_field_index)).with_frame_context(Some(&state))?;

                    state.push_stack_check_overflow(field_value)?;
                }
                GospelOpcode::StructSetLocalField => {
                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;

                    let field_value = state.pop_stack_check_underflow()?;
                    let mut struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;
                    state.validate_struct_instance_template(&struct_value, &struct_template)?;

                    let struct_field_index = state.immediate_value_checked(instruction, 1)? as usize;
                    struct_value.set_raw_property(struct_field_index, Some(field_value)).with_frame_context(Some(&state))?;

                    state.push_stack_check_overflow(GospelVMValue::Struct(struct_value))?;
                }
                GospelOpcode::StructGetNamedField => {
                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;

                    let struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;
                    state.validate_struct_instance_template(&struct_value, &struct_template)?;

                    let struct_field_name_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let struct_field_name = state.copy_referenced_string_checked(struct_field_name_index)?;

                    let field_value = struct_value.take_named_property(struct_field_name.as_str()).with_frame_context(Some(&state))?
                        .ok_or_else(|| anyhow!("Field {} is not set on struct instance", struct_field_name)).with_frame_context(Some(&state))?;
                    state.push_stack_check_overflow(field_value)?;
                }
                GospelOpcode::StructSetNamedField => {
                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;

                    let field_value = state.pop_stack_check_underflow()?;
                    let mut struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;
                    state.validate_struct_instance_template(&struct_value, &struct_template)?;

                    let struct_field_name_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let struct_field_name = state.copy_referenced_string_checked(struct_field_name_index)?;

                    struct_value.set_named_property(struct_field_name.as_str(), Some(field_value)).with_frame_context(Some(&state))?;
                    state.push_stack_check_overflow(GospelVMValue::Struct(struct_value))?;
                }
                GospelOpcode::StructIsStructOfType => {
                    let struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;

                    let struct_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let struct_template = state.get_referenced_struct_checked(struct_index)?;

                    let result = if Rc::ptr_eq(&struct_value.template, &struct_template) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::StructGetNamedTypedField => {
                    let field_expected_value_type = GospelValueType::from_repr(state.immediate_value_checked(instruction, 0)? as u8)
                        .ok_or_else(|| vm_error!(Some(&state), "Unknown value type"))?;

                    let struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;

                    let struct_field_name_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let struct_field_name = state.copy_referenced_string_checked(struct_field_name_index)?;

                    let struct_field_index = struct_value.template.find_named_property_index(&struct_field_name)
                        .ok_or_else(|| vm_error!(Some(&state), "Struct does not have a property with name '{}'", struct_field_name))?;
                    let struct_field_type = struct_value.template.fields[struct_field_index].0;
                    if struct_field_type != field_expected_value_type {
                        vm_bail!(Some(&state), "Expected field {} value to be of type {}, but it was of type {}", struct_field_name, field_expected_value_type, struct_field_type);
                    }

                    let field_value = struct_value.take_raw_property(struct_field_index).with_frame_context(Some(&state))?
                        .ok_or_else(|| vm_error!(Some(&state), "Field {} is not set on struct instance", struct_field_name))?;
                    state.push_stack_check_overflow(field_value)?;
                }
                GospelOpcode::StructSetNamedTypedField => {
                    let field_expected_value_type = GospelValueType::from_repr(state.immediate_value_checked(instruction, 0)? as u8)
                        .ok_or_else(|| vm_error!(Some(&state), "Unknown value type"))?;

                    let field_value = state.pop_stack_check_underflow()?;
                    let mut struct_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;

                    let struct_field_name_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let struct_field_name = state.copy_referenced_string_checked(struct_field_name_index)?;

                    let struct_field_index = struct_value.template.find_named_property_index(&struct_field_name)
                        .ok_or_else(|| vm_error!(Some(&state), "Struct does not have a property with name '{}'", struct_field_name))?;
                    let struct_field_type = struct_value.template.fields[struct_field_index].0;
                    if struct_field_type != field_expected_value_type {
                        vm_bail!(Some(&state), "Expected field {} value to be of type {}, but it was of type {}", struct_field_name, field_expected_value_type, struct_field_type);
                    }

                    struct_value.set_raw_property(struct_field_index, Some(field_value)).with_frame_context(Some(&state))?;
                    state.push_stack_check_overflow(GospelVMValue::Struct(struct_value))?;
                }
            };
        }
        // Function should always at the very least return a value, empty function code or fall through without return is an error
        vm_bail!(Some(&state), "Function failed to return a value");
    }
}

#[derive(Debug)]
pub struct GospelVMContainer {
    target_triplet: GospelVMTargetTriplet,
    container: Rc<GospelContainer>,
    external_references: Vec<Rc<GospelVMContainer>>,
    global_lookup_by_id: HashMap<usize, Rc<GospelGlobalStorage>>,
    function_lookup_by_name: HashMap<String, u32>,
    struct_lookup_by_name: HashMap<String, u32>,
    struct_templates: Vec<Rc<GospelVMStructTemplate>>,
}
impl GospelVMContainer {
    /// Returns the name of this type container
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.container.container_name()
    }
    /// Attempts to find a function with the given name in this container and returns a reference to it
    pub fn find_named_function(self: &Rc<Self>, name: &str) -> Option<GospelVMClosure> {
        self.function_lookup_by_name.get(name).map(|type_index| GospelVMClosure {
            container: self.clone(), function_index: *type_index, arguments: Vec::new() })
    }
    fn find_named_function_exported(self: &Rc<Self>, name: &str) -> Option<GospelVMClosure> {
        self.function_lookup_by_name.get(name)
            .filter(|function_index| self.container.functions[**function_index as usize].exported)
            .map(|type_index| GospelVMClosure { container: self.clone(), function_index: *type_index, arguments: Vec::new() })
    }
    /// Attempts to find a named struct definition with the given name in this container
    pub fn find_named_struct(self: &Rc<Self>, name: &str) -> Option<Rc<GospelVMStructTemplate>> {
        self.struct_lookup_by_name.get(name).map(|struct_index| self.struct_templates[*struct_index as usize].clone())
    }
    fn find_named_struct_exported(self: &Rc<Self>, name: &str) -> Option<Rc<GospelVMStructTemplate>> {
        self.struct_lookup_by_name.get(name)
            .filter(|struct_index| self.container.structs[**struct_index as usize].exported)
            .map(|struct_index| self.struct_templates[*struct_index as usize].clone())
    }
    fn resolve_function_index(self: &Rc<Self>, function_index: GospelObjectIndex) -> anyhow::Result<GospelVMClosure> {
        match function_index {
            GospelObjectIndex::External(external_index) => {
                if external_index as usize >= self.container.external_functions.len() {
                    bail!("Invalid external function index #{} out of bounds (num external function references in container: {})", external_index, self.container.external_functions.len());
                }
                let external_function = &self.container.external_functions[external_index as usize];
                if external_function.import_index as usize >= self.external_references.len() {
                    bail!("Invalid external container reference index #{} out of bounds (num external container references: {})", external_function.import_index, self.external_references.len());
                }
                let source_container = &self.external_references[external_function.import_index as usize];
                let type_name = self.container.strings.get(external_function.object_name)?;
                source_container.find_named_function_exported(type_name)
                    .ok_or_else(|| { anyhow!("Imported named function {} does not exist in container {}", self.container_name().unwrap(), type_name.to_string()) })
            }
            GospelObjectIndex::Local(local_index) => {
                Ok(GospelVMClosure { container: self.clone(), function_index: local_index, arguments: Vec::new() })
            }
        }
    }
    fn resolve_static_value(self: &Rc<Self>, value: &GospelStaticValue) -> anyhow::Result<GospelVMValue> {
        match value {
            GospelStaticValue::Integer(integer_value) => {
                Ok(GospelVMValue::Integer(*integer_value))
            }
            GospelStaticValue::FunctionIndex(function_index) => {
                let reference = self.resolve_function_index(*function_index)?;
                Ok(GospelVMValue::Closure(reference))
            }
            GospelStaticValue::GlobalVariableValue(global_variable_index) => {
                let global_variable = self.global_lookup_by_id.get(&(*global_variable_index as usize))
                    .ok_or_else(|| anyhow!("Failed to find global with index specified"))?;
                // Make sure the global variable has been initialized
                let current_value = global_variable.current_value.borrow().clone()
                    .ok_or_else(|| anyhow!("Attempt to read uninitialized global variable {}", global_variable.name))?;
                Ok(GospelVMValue::Integer(current_value))
            }
            GospelStaticValue::PlatformConfigProperty(config_property) => {
                let resolved_value = self.target_triplet.resolve_platform_config_property(*config_property);
                Ok(GospelVMValue::Integer(resolved_value))
            }
        }
    }
    fn resolve_slot_binding(self: &Rc<Self>, type_definition: &GospelFunctionDefinition, slot: &GospelSlotDefinition, args: &Vec<GospelVMValue>) -> anyhow::Result<Option<GospelVMValue>> {
        match slot.binding {
            GospelSlotBinding::Uninitialized => {
                Ok(None)
            }
            GospelSlotBinding::StaticValue(static_value) => {
                let resolved_value = self.resolve_static_value(&static_value)?;
                if slot.value_type != resolved_value.value_type() {
                    bail!("Slot value type is not compatible with static value type specified")
                }
                Ok(Some(resolved_value))
            }
            GospelSlotBinding::ArgumentValue(argument_index) => {
                if argument_index as usize >= type_definition.arguments.len() {
                    bail!("Invalid template argument index #{} (number of template arguments: {})", argument_index, type_definition.arguments.len());
                }
                if type_definition.arguments[argument_index as usize].argument_type != slot.value_type {
                    bail!("Incompatible value type for slot and argument at index #{}", argument_index);
                }
                let resolved_value = if argument_index as usize >= args.len() {
                    bail!("Missing value for argument #{}", argument_index);
                } else {
                    args[argument_index as usize].clone()
                };
                if resolved_value.value_type() != type_definition.arguments[argument_index as usize].argument_type {
                    bail!("Incompatible value type for argument type and provided value");
                }
                Ok(Some(resolved_value))
            }
        }
    }
    fn resolve_struct_template(self: &Rc<Self>, struct_index: &GospelObjectIndex) -> anyhow::Result<Rc<GospelVMStructTemplate>> {
        match struct_index {
            GospelObjectIndex::External(external_index) => {
                if *external_index as usize >= self.container.external_structs.len() {
                    bail!("Invalid external struct index #{} out of bounds (num external struct references in container: {})", *external_index, self.container.external_structs.len());
                }
                let external_struct = &self.container.external_structs[*external_index as usize];
                if external_struct.import_index as usize >= self.external_references.len() {
                    bail!("Invalid external container reference index #{} out of bounds (num external container references: {})", external_struct.import_index, self.external_references.len());
                }
                let source_container = &self.external_references[external_struct.import_index as usize];
                let struct_name = self.container.strings.get(external_struct.object_name)?;
                source_container.find_named_struct_exported(struct_name)
                    .ok_or_else(|| { anyhow!("Imported named struct {} does not exist in container {}", self.container_name().unwrap(), struct_name.to_string()) })
            }
            GospelObjectIndex::Local(local_index) => {
                if *local_index as usize >= self.struct_templates.len() {
                    bail!("Invalid struct index #{} out of bounds (num structs in container: {})", *local_index, self.struct_templates.len());
                }
                Ok(self.struct_templates[*local_index as usize].clone())
            }
        }
    }
    fn execute_function_internal(self: &Rc<Self>, index: u32, args: &Vec<GospelVMValue>, previous_frame: Option<&GospelVMExecutionState>) -> GospelVMResult<GospelVMValue> {
        if index as usize >= self.container.functions.len() {
            vm_bail!(previous_frame, "Invalid function index #{} out of bounds (num functions in container: {})", index, self.container.functions.len());
        }
        let function_definition = &self.container.functions[index as usize];

        // Construct a fresh VM state
        let mut vm_state = GospelVMExecutionState{
            owner_container: self,
            function_definition: &function_definition,
            slots: Vec::with_capacity(function_definition.slots.len()),
            referenced_strings: Vec::with_capacity(function_definition.referenced_strings.len()),
            referenced_structs: Vec::with_capacity(function_definition.referenced_structs.len()),
            stack: Vec::new(),
            current_instruction_index: 0,
            current_loop_jump_count: 0,
            recursion_counter: previous_frame.map(|x| x.recursion_counter).unwrap_or(0),
            previous_frame,
            max_stack_size: 256, // TODO: Make limits configurable
            max_loop_jumps: 8192,
            max_recursion_depth: 128,
        };

        // Populate slots with their initial values
        for slot_index in 0..function_definition.slots.len() {
            let slot_value = self.resolve_slot_binding(function_definition, &function_definition.slots[slot_index], args)
            .map_err(|x| vm_error!(previous_frame, "Failed to bind slot #{} value: {}", slot_index, x.to_string()))?;
            vm_state.slots.push(slot_value)
        }

        // Populate referenced strings
        for string_index in &function_definition.referenced_strings {
            vm_state.referenced_strings.push(self.container.strings.get(*string_index).with_frame_context(previous_frame)?.to_string());
        }

        // Populate referenced structs
        for struct_index in &function_definition.referenced_structs {
            vm_state.referenced_structs.push(self.resolve_struct_template(struct_index).with_frame_context(previous_frame)?);
        }

        // Run the VM now to calculate the result of the function
        GospelVMExecutionState::run(&mut vm_state)
    }
    /// Creates a module reflector from this container
    pub fn reflect(self: &Rc<Self>) -> anyhow::Result<Box<dyn GospelModuleReflector>> {
        Ok(Box::new(GospelContainerReflector::create(self.container.clone())?))
    }
}

/// VM state for the Gospel VM
/// Containers can be injected into the VM to register type definitions
/// Global variables can be defined to supply additional information to the type definitions.
/// Function definitions can be retrieved with find_named_function
/// WARNING: VM instances are NOT thread safe, and must be wrapped into RWLock to be safely usable concurrently
pub struct GospelVMState {
    target_triplet: GospelVMTargetTriplet,
    containers: Vec<Rc<GospelVMContainer>>,
    containers_by_name: HashMap<String, Rc<GospelVMContainer>>,
    globals_by_name: HashMap<String, Rc<GospelGlobalStorage>>,
}
impl GospelVMState {

    /// Creates a new, blank VM state with the provided platform config
    /// Type contains must be mounted to the VM by calling mount_container
    pub fn create(target_triplet: GospelVMTargetTriplet) -> Self {
        Self{target_triplet, containers: Vec::new(), containers_by_name: HashMap::new(), globals_by_name: HashMap::new()}
    }

    /// Adds a new gospel container to the VM. Returns the created container
    pub fn mount_container(&mut self, container: GospelContainer) -> anyhow::Result<Rc<GospelVMContainer>> {
        let wrapped_container = Rc::new(container);
        let container_name = wrapped_container.container_name()?.to_string();
        if self.containers_by_name.get(&container_name).is_some() {
            bail!("Container with name {} is already mounted", container_name);
        }

        // Resolve imports necessary to construct external types down the line
        let mut external_references: Vec<Rc<GospelVMContainer>> = Vec::new();
        for import_index in 0..wrapped_container.imports.len() {
            let import_container_name = wrapped_container.strings.get(wrapped_container.imports[import_index].container_name)?;
            let resolved_import = self.find_named_container(import_container_name)
                .ok_or_else(|| { anyhow!("Cannot mount container {} because it depends on container {} that is not mounted", container_name, import_container_name) })?;
            external_references.push(resolved_import);
        }

        let mut vm_container = GospelVMContainer{
            target_triplet: self.target_triplet.clone(),
            container: wrapped_container.clone(),
            external_references,
            global_lookup_by_id: HashMap::new(),
            function_lookup_by_name: HashMap::new(),
            struct_templates: Vec::new(),
            struct_lookup_by_name: HashMap::new(),
        };

        // Build lookup table for functions by name, and create globals referenced by the container
        for function_index in 0..wrapped_container.functions.len() {
            let function_name = wrapped_container.strings.get(wrapped_container.functions[function_index].name)?;
            vm_container.function_lookup_by_name.insert(function_name.to_string(), function_index as u32);
        }
        for global_index in 0..wrapped_container.globals.len() {
            let global_name = wrapped_container.strings.get(wrapped_container.globals[global_index].name)?;
            let initial_value = wrapped_container.globals[global_index].default_value;

            let global_value = self.find_or_create_global(global_name, initial_value)?;
            vm_container.global_lookup_by_id.insert(global_index, global_value);
        }
        
        // Build struct templates for structs defined in the container
        let mut struct_templates: Vec<GospelVMStructTemplate> = Vec::with_capacity(wrapped_container.structs.len());
        for struct_index in 0..wrapped_container.structs.len() {
            let struct_definition = &wrapped_container.structs[struct_index];
            let struct_template = GospelVMStructTemplate{
                fields: struct_definition.fields.iter().map(|x| {
                    (x.field_type, wrapped_container.strings.get(x.field_name).unwrap_or("<unnamed>").to_string())
                }).collect(),
                source_container_name: container_name.clone(),
                name: None,
                property_index_lookup: struct_definition.fields.iter().enumerate().filter_map(|(index, x)| {
                    wrapped_container.strings.get(x.field_name).ok().map(|y| (y.to_string(), index))
                }).collect(),
            };
            struct_templates.push(struct_template);
        }
        vm_container.struct_templates = struct_templates.into_iter().map(|x| Rc::new(x)).collect();

        // Finally, add container to the mounted container list
        let wrapped_vm_container = Rc::new(vm_container);
        self.containers.push(wrapped_vm_container.clone());
        self.containers_by_name.insert(container_name, wrapped_vm_container.clone());

        Ok(wrapped_vm_container)
    }

    /// Returns the target triplet being used by this VM instance
    pub fn get_platform_config(&self) -> GospelVMTargetTriplet {
        self.target_triplet.clone()
    }

    /// Returns a list of modules currently loaded into this VM instance
    pub fn enumerate_modules(&self) -> Vec<Rc<GospelVMContainer>> {
        self.containers.clone()
    }

    /// Reads the current value of a global variable by name, returns None if variable does not exist or is not currently assigned
    pub fn read_global_value(&self, name: &str) -> Option<i32> {
        self.globals_by_name.get(name).and_then(|x| *x.current_value.borrow())
    }

    /// Assigns the value to the global variable by name. Defines a new global variable if it has not been defined yet
    pub fn set_global_value(&mut self, name: &str, new_value: i32) -> anyhow::Result<()> {
        let global_storage = self.find_or_create_global(name, None)?;
        global_storage.current_value.replace(Some(new_value));
        Ok({})
    }

    /// Returns a container by name
    pub fn find_named_container(&self, name: &str) -> Option<Rc<GospelVMContainer>> {
        self.containers_by_name.get(name).map(|x| x.clone())
    }

    /// Returns a value of the global variable by name if it is defined and has a value, or None otherwise
    pub fn get_global_variable_value(&self, name: &str) -> Option<i32> {
        self.globals_by_name.get(name).and_then(|global_storage| global_storage.current_value.borrow().clone())
    }

    /// Attempts to find a function definition by its fully qualified name (container name combined with function name)
    /// Providing the container context allows resolving local function references as well
    pub fn find_function_by_reference(&self, reference: &GospelSourceObjectReference) -> Option<GospelVMClosure> {
        self.find_named_container(reference.module_name.as_str()).and_then(|container| container.find_named_function(reference.local_name.as_str()))
    }

    /// Allows evaluating a source value without building a container first (REPL-like API)
    pub fn eval_source_value(&self, value: &GospelSourceStaticValue) -> anyhow::Result<GospelVMValue> {
        match value {
            GospelSourceStaticValue::FunctionId(function_reference) => {
                self.find_function_by_reference(&function_reference)
                    .map(|function_pointer| GospelVMValue::Closure(function_pointer))
                    .ok_or_else(|| anyhow!("Failed to find function by function reference {}", function_reference))
            }
            GospelSourceStaticValue::GlobalVariableValue(global_variable_name) => {
                self.get_global_variable_value(global_variable_name.as_str())
                    .map(|integer_value| GospelVMValue::Integer(integer_value))
                    .ok_or_else(|| anyhow!("Global variable named {} is not defined or does not have a value assigned", global_variable_name))
            }
            GospelSourceStaticValue::Integer(integer_value) => {
                Ok(GospelVMValue::Integer(*integer_value))
            }
            GospelSourceStaticValue::PlatformConfigProperty(config_property) => {
                Ok(GospelVMValue::Integer(self.target_triplet.resolve_platform_config_property(*config_property)))
            }
        }
    }

    fn find_or_create_global(&mut self, name: &str, initial_value: Option<i32>) -> anyhow::Result<Rc<GospelGlobalStorage>> {
        if let Some(existing_global) = self.globals_by_name.get(name) {
            if let Some(unwrapped_initial_value) = initial_value {
                let mut current_initial_value = existing_global.initial_value.borrow_mut();

                // Validate that the initial value is the same as the provided one
                if let Some(unwrapped_current_initial_value) = *current_initial_value {
                    if unwrapped_current_initial_value != unwrapped_initial_value {
                        bail!("Incompatible default values for global variable {}: current default value is {}, but new default value is {}",
                            name.to_string(), unwrapped_current_initial_value, unwrapped_initial_value);
                    }
                } else {
                    // Current initial value becomes the new initial value for this variable
                    *current_initial_value = Some(unwrapped_initial_value);

                    // If current value is not set, the new initial value takes over
                    let mut current_value = existing_global.current_value.borrow_mut();
                    if current_value.is_none() {
                        *current_value = Some(unwrapped_initial_value);
                    }
                }
            }
            return Ok(existing_global.clone())
        }

        // Create a new global storage with initial value as the current value
        let new_global = Rc::new(GospelGlobalStorage{
            name: name.to_string(),
            initial_value: RefCell::new(initial_value),
            current_value: RefCell::new(initial_value),
        });
        self.globals_by_name.insert(name.to_string(), new_global.clone());
        Ok(new_global)
    }
}
