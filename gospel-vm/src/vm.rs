use std::cell::RefCell;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::DerefMut;
use std::rc::{Rc};
use std::str::FromStr;
use anyhow::{anyhow, bail};
use strum::Display;
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::module::GospelContainer;
use crate::gospel::{GospelFunctionDefinition, GospelObjectIndex, GospelValueType, GospelTargetProperty};
use crate::writer::{GospelSourceObjectReference};
use serde::{Deserialize, Serialize, Serializer};
use serde::ser::SerializeStruct;
use gospel_typelib::type_model::{ArrayType, CVQualifiedType, FunctionType, PointerType, PrimitiveType, ResolvedUDTMemberLayout, TargetTriplet, Type, TypeGraphLike, UserDefinedType, UserDefinedTypeBitfield, UserDefinedTypeField, UserDefinedTypeKind, UserDefinedTypeMember, FunctionDeclaration, FunctionParameterDeclaration, TypeLayoutCache, EnumType, EnumKind, EnumConstant};
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

/// Options for Gospel VM code evaluation
#[derive(Debug, Clone)]
pub struct GospelVMOptions {
    target_triplet: Option<TargetTriplet>,
    no_default_globals: bool,
    globals: HashMap<String, i32>,
}
impl Default for GospelVMOptions {
    fn default() -> Self {
        Self{target_triplet: None, no_default_globals: false, globals: HashMap::new()}
    }
}
impl GospelVMOptions {
    /// Sets the target triplet for the VM. Target triplet is required to evaluate type sizes and layouts
    pub fn target_triplet(mut self, target_triplet: TargetTriplet) -> Self {
        self.target_triplet = Some(target_triplet); self
    }
    /// Disable default values assigned by the modules to the global variables. All variable values have to be set on the context explicitly. Accessing an unset global results in an exception
    pub fn no_default_globals(mut self) -> Self {
        self.no_default_globals = true; self
    }
    /// Sets the given global variable to the value provided. Overrides the default value for the given global if one exists
    pub fn with_global(mut self, name: &str, value: i32) -> Self {
        self.globals.insert(name.to_string(), value); self
    }
}

/// Wrapper for Types that also contains metadata maintained by the VM
#[derive(Debug, Clone)]
pub struct GospelVMTypeContainer {
    pub wrapped_type: Type,
    pub base_class_prototypes: Option<HashSet<usize>>,
    pub member_prototypes: Option<HashSet<UserDefinedTypeMember>>,
    pub enum_constant_prototypes: Option<HashSet<String>>,
    pub vm_metadata: Option<GospelVMStruct>,
    pub partial_type: bool,
    owner_stack_frame_token: usize,
    size_has_been_validated: bool,
}

/// Run context allows caching results of function invocations and creating type graphs from individual types
#[derive(Debug)]
pub struct GospelVMRunContext {
    options: GospelVMOptions,
    types: Vec<GospelVMTypeContainer>,
    simple_type_lookup: HashMap<Type, usize>,
    call_result_lookup: HashMap<GospelVMClosure, Rc<RefCell<Option<GospelVMValue>>>>,
    stack_frame_counter: usize,
}
impl GospelVMRunContext {
    /// Creates new run context from the specified VM options
    pub fn create(options: GospelVMOptions) -> GospelVMRunContext {
        GospelVMRunContext{options, types: Vec::new(), simple_type_lookup: HashMap::new(), call_result_lookup: HashMap::new(), stack_frame_counter: 1}
    }
    /// Returns the target triplet associated with this run context
    pub fn target_triplet(&self) -> Option<&TargetTriplet> {
        self.options.target_triplet.as_ref()
    }
    /// Returns the type container for the type at the given index. Type container contains additional metadata tracked by the VM that might be useful in some cases
    pub fn type_container_by_index(&self, type_index: usize) -> &GospelVMTypeContainer {
        &self.types[type_index]
    }
    /// Stores type to the VM run context. This can be used to pass external types constructed outside to the VM
    pub fn store_type(&mut self, type_data: Type) -> usize {
        if let Some(existing_type_index) = self.simple_type_lookup.get(&type_data) {
            *existing_type_index
        } else {
            let new_type_index = self.types.len();
            // Simple types cannot have VM metadata assigned to them
            self.types.push(GospelVMTypeContainer {wrapped_type: type_data.clone(), base_class_prototypes: None, member_prototypes: None, enum_constant_prototypes: None,
                vm_metadata: None, owner_stack_frame_token: 0, size_has_been_validated: false, partial_type: false});
            self.simple_type_lookup.insert(type_data, new_type_index);
            new_type_index
        }
    }
    fn read_global_value(&self, global_name: &str, default_value: Option<i32>) -> Option<i32> {
        if let Some(global_value_override) = self.options.globals.get(global_name) {
            Some(*global_value_override)
        } else if let Some(default_global_value) = default_value && !self.options.no_default_globals {
            Some(default_global_value)
        } else { None }
    }
    fn new_stack_frame_token(&mut self) -> usize {
        let result_stack_frame_token = self.stack_frame_counter;
        self.stack_frame_counter += 1;
        result_stack_frame_token
    }
    fn store_unique_named_type(&mut self, type_data: Type, stack_frame_token: usize) -> usize {
        let new_type_index = self.types.len();
        self.types.push(GospelVMTypeContainer{wrapped_type: type_data, base_class_prototypes: Some(HashSet::new()), member_prototypes: Some(HashSet::new()), enum_constant_prototypes: Some(HashSet::new()),
            vm_metadata: None, owner_stack_frame_token: stack_frame_token, size_has_been_validated: false, partial_type: false});
        new_type_index
    }
    fn validate_type_not_partial(&mut self, type_index: usize, source_frame: Option<&GospelVMExecutionState>) -> GospelVMResult<()> {
        let mut type_size_calculation_stack: Vec<usize> = Vec::new();
        if self.validate_type_internal(type_index, source_frame, &mut type_size_calculation_stack)? {
            return Err(vm_error!(source_frame, "Type at index #{} is a partial type", type_index));
        }
        Ok({})
    }
    fn validate_type_internal(&mut self, type_index: usize, source_frame: Option<&GospelVMExecutionState>, type_size_calculation_stack: &mut Vec<usize>) -> GospelVMResult<bool> {
        if self.types[type_index].size_has_been_validated {
            return Ok(self.types[type_index].partial_type)
        }
        let type_name = if let Type::UDT(udt) = &self.types[type_index].wrapped_type {
            udt.name.as_ref().map(|x| x.as_str()).unwrap_or("<unnamed udt>")
        } else { "<non udt type>" };
        if self.types[type_index].owner_stack_frame_token != 0 {
            return Err(vm_error!(source_frame, "Type at index #{} ({}) has been declared but has not been defined yet (is finalization pass: {})", type_index, type_name, source_frame.is_none()))
        }
        if type_size_calculation_stack.contains(&type_index) {
            return Err(vm_error!(source_frame, "Type at index #{} ({}) has infinite size", type_index, type_name));
        }
        type_size_calculation_stack.push(type_index);

        let mut is_partial_type = self.types[type_index].partial_type;
        let cloned_type = self.types[type_index].wrapped_type.clone();
        match cloned_type {
            Type::Array(array_type) => {
                is_partial_type |= self.validate_type_internal(array_type.element_type_index, source_frame, type_size_calculation_stack)?;
            }
            Type::CVQualified(cv_qualified_type) => {
                is_partial_type |= self.validate_type_internal(cv_qualified_type.base_type_index, source_frame, type_size_calculation_stack)?;
            }
            Type::UDT(user_defined_type) => {
                for base_class_index in &user_defined_type.base_class_indices {
                    is_partial_type |= self.validate_type_internal(*base_class_index, source_frame, type_size_calculation_stack)?;
                }
                for member in &user_defined_type.members {
                    if let UserDefinedTypeMember::Field(field) = member {
                        is_partial_type |= self.validate_type_internal(field.member_type_index, source_frame, type_size_calculation_stack)?;
                    }
                }
            }
            _ => {}
        };
        type_size_calculation_stack.pop();
        self.types[type_index].size_has_been_validated = true;
        self.types[type_index].partial_type = is_partial_type;

        // If this is a partial UDT type, add member of void type to prevent layout of this type from being ever calculated, even by external code
        if is_partial_type {
            let void_type_index = self.store_type(Type::Primitive(PrimitiveType::Void));
            if let Type::UDT(user_defined_type) = &mut self.types[type_index].wrapped_type {
                user_defined_type.members.push(UserDefinedTypeMember::Field(UserDefinedTypeField{
                    name: Some(String::from("@__gospel_partial_type_marker")), user_alignment: None, member_type_index: void_type_index,
                }));
            }
        }
        Ok(is_partial_type)
    }
    fn check_all_types_validated(&mut self) -> GospelVMResult<()> {
        for type_index in 0..self.types.len() {
            if !self.types[type_index].size_has_been_validated {
                let mut type_size_calculation_stack: Vec<usize> = Vec::new();
                self.validate_type_internal(type_index, None, &mut type_size_calculation_stack)?;
            }
        }
        Ok({})
    }
}
impl TypeGraphLike for GospelVMRunContext {
    fn type_by_index(&self, type_index: usize) -> &Type {
        &self.types[type_index].wrapped_type
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
impl Hash for GospelVMClosure {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let container_ptr = Rc::as_ptr(&self.container);
        container_ptr.hash(state);
        self.function_index.hash(state);
        self.arguments.hash(state);
    }
}
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
    /// Returns metadata for the function this closure is created from by the metadata key. Returns none if metadata with that key is not available
    pub fn function_metadata(&self, key: &str) -> Option<&str> {
        if (self.function_index as usize) < self.container.container.functions.len() {
            let function_definition = &self.container.container.functions[self.function_index as usize];
            let metadata_entry = function_definition.metadata.iter().find(|x| self.container.container.strings.get(x.metadata_key).ok() == Some(key));
            metadata_entry.and_then(|x| self.container.container.strings.get(x.metadata_value).ok())
        } else { None }
    }
    /// Attempts to execute this closure and returns the result
    pub fn execute(&self, args: Vec<GospelVMValue>, run_context: &mut GospelVMRunContext) -> GospelVMResult<GospelVMValue> {
        let execution_result = self.execute_internal(args, run_context, None)?;
        run_context.check_all_types_validated()?; // user code outside the VM should never see types with invalid sizes
        Ok(execution_result)
    }
    fn execute_internal(&self, args: Vec<GospelVMValue>, run_context: &mut GospelVMRunContext, previous_frame: Option<&GospelVMExecutionState>) -> GospelVMResult<GospelVMValue> {
        if self.arguments.is_empty() {
            self.container.execute_function_cached_internal(self.function_index, &args, run_context, previous_frame)
        } else if args.is_empty() {
            self.container.execute_function_cached_internal(self.function_index, &self.arguments, run_context, previous_frame)
        } else {
            let mut concat_args = self.arguments.clone();
            concat_args.extend(args.into_iter());
            self.container.execute_function_cached_internal(self.function_index, &concat_args, run_context, previous_frame)
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
impl Hash for GospelVMStruct {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fields.hash(state);
        let template_ptr = Rc::as_ptr(&self.template);
        template_ptr.hash(state);
    }
}
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, Display, Serialize)]
pub enum GospelVMValue {
    #[strum(to_string = "Integer({0})")]
    Integer(i32), // signed 32-bit integer value
    #[strum(to_string = "Closure({0})")]
    Closure(GospelVMClosure), // pointer to a function with some number (or no) arguments captured with it
    #[strum(to_string = "TypeLayout({0})")]
    TypeReference(usize), // index of the type in the current run context
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
            GospelVMValue::TypeReference(_) => { GospelValueType::TypeReference }
            GospelVMValue::Array(_) => { GospelValueType::Array }
            GospelVMValue::Struct(_) => { GospelValueType::Struct }
        }
    }
}

#[derive(Debug, Default)]
struct GospelGlobalStorage {
    global_defaults: RefCell<HashMap<String, i32>>,
}
impl GospelGlobalStorage {
    fn set_global_default_value(&self, name: &str, default_value: i32) -> anyhow::Result<()> {
        if let Some(existing_value) = self.global_defaults.borrow().get(name) {
            if *existing_value != default_value {
                bail!("Incompatible default values for global variable {}: current default value is {}, but new default value is {}",name, *existing_value, default_value);
            }
            Ok({})
        } else {
            self.global_defaults.borrow_mut().insert(name.to_string(), default_value);
            Ok({})
        }
    }
    fn find_default_global_value(&self, name: &str) -> Option<i32> {
        self.global_defaults.borrow().get(name).cloned()
    }
}

#[derive(Debug)]
struct GospelExceptionHandler {
    #[allow(dead_code)]
    start_instruction_index: usize,
    start_stack_snapshot: Vec<GospelVMValue>,
    target_instruction_index: usize,
}

#[derive(Debug)]
struct GospelVMExecutionState<'a> {
    owner_container: &'a Rc<GospelVMContainer>,
    function_definition: &'a GospelFunctionDefinition,
    argument_values: &'a Vec<GospelVMValue>,
    slots: Vec<Option<GospelVMValue>>,
    referenced_strings: Vec<&'a str>,
    referenced_structs: Vec<Rc<GospelVMStructTemplate>>,
    referenced_functions: Vec<GospelVMClosure>,
    stack: Vec<GospelVMValue>,
    exception_handler_stack: Vec<GospelExceptionHandler>,
    current_instruction_index: usize,
    current_loop_jump_count: usize,
    return_value_slot: Rc<RefCell<Option<GospelVMValue>>>,
    stack_frame_token: usize,
    previous_frame: Option<&'a GospelVMExecutionState<'a>>,
    collapsed_call_chain: RefCell<HashSet<GospelVMClosure>>,
    type_count_at_function_start: usize,
    recursion_counter: usize,
    max_stack_size: usize,
    max_loop_jumps: usize,
    max_recursion_depth: usize,
    max_exception_handler_depth: usize,
}
impl<'a> GospelVMExecutionState<'a> {
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
    fn copy_argument_value_checked(&mut self, index: usize) -> GospelVMResult<GospelVMValue> {
        if index >= self.argument_values.len() {
            vm_bail!(Some(self), "Missing value for argument #{} (number of arguments: {})", index, self.argument_values.len());
        }
        Ok(self.argument_values[index].clone())
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
        self.slots[index] = Some(value);
        Ok({})
    }
    fn immediate_value_checked(&self, inst: &GospelInstruction, index: usize) -> GospelVMResult<u32> {
        inst.immediate_operand_at(index).ok_or_else(|| vm_error!(Some(self), "Invalid instruction encoding: Missing immediate operand #{}", index))
    }
    fn get_referenced_string_checked(&self, index: usize) -> GospelVMResult<&'a str> {
        if index >= self.referenced_strings.len() {
            vm_bail!(Some(self), "Invalid referenced string index #{} out of bounds (number of referenced strings: {})", index, self.referenced_strings.len());
        }
        Ok(self.referenced_strings[index])
    }
    fn get_referenced_struct_checked(&self, index: usize) -> GospelVMResult<Rc<GospelVMStructTemplate>> {
        if index >= self.referenced_structs.len() {
            vm_bail!(Some(self), "Invalid referenced struct index #{} out of bounds (number of referenced structs: {})", index, self.referenced_structs.len());
        }
        Ok(self.referenced_structs[index].clone())
    }
    fn get_referenced_function_checked(&self, index: usize) -> GospelVMResult<GospelVMClosure> {
        if index >= self.referenced_functions.len() {
            vm_bail!(Some(self), "Invalid referenced function index #{} out of bounds (number of referenced functions: {})", index, self.referenced_functions.len());
        }
        Ok(self.referenced_functions[index].clone())
    }
    fn unwrap_value_as_int_checked(&self, value: GospelVMValue) -> GospelVMResult<i32> {
        match value {
            GospelVMValue::Integer(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected integer value, got value of type {}", value.value_type()))
        }
    }
    fn unwrap_value_as_closure_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelVMClosure> {
        match value {
            GospelVMValue::Closure(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected function pointer, got value of type {}", value.value_type()))
        }
    }
    fn unwrap_value_as_array_checked(&self, value: GospelVMValue) -> GospelVMResult<Vec<GospelVMValue>> {
        match value {
            GospelVMValue::Array(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected array value, got value of type {}", value.value_type()))
        }
    }
    fn unwrap_value_as_struct_checked(&self, value: GospelVMValue) -> GospelVMResult<GospelVMStruct> {
        match value {
            GospelVMValue::Struct(unwrapped) => { Ok(unwrapped) }
            _ => Err(vm_error!(Some(self), "Expected struct value, got value of type {}", value.value_type()))
        }
    }
    fn validate_type_not_finalized(&self, type_index: usize, run_context: &GospelVMRunContext) -> GospelVMResult<()> {
        if run_context.types[type_index].owner_stack_frame_token == self.stack_frame_token {
            Ok({})
        } else {
            Err(vm_error!(Some(self), "Type at index #{} is not owned by the current stack frame and cannot be modified", type_index))
        }
    }
    fn validate_type_index_user_defined_type(&self, type_index: usize, run_context: &GospelVMRunContext) -> GospelVMResult<usize> {
        if let Type::UDT(_) = run_context.type_by_index(type_index) {
            Ok(type_index)
        } else {
            Err(vm_error!(Some(self), "Expected user-defined type at index #{}, got another type", type_index))
        }
    }
    fn validate_type_index_enum_type(&self, type_index: usize, run_context: &GospelVMRunContext) -> GospelVMResult<usize> {
        if let Type::Enum(_) = run_context.type_by_index(type_index) {
            Ok(type_index)
        } else {
            Err(vm_error!(Some(self), "Expected enum type at index #{}, got another type", type_index))
        }
    }
    fn new_type_layout_cache(&self, run_context: &GospelVMRunContext) -> GospelVMResult<TypeLayoutCache> {
        if let Some(target_triplet) = run_context.target_triplet() {
            Ok(TypeLayoutCache::create(target_triplet.clone()))
        } else {
            vm_bail!(Some(self), "Target triplet not set for type layout calculation");
        }
    }
    fn unwrap_value_as_type_index_checked(&self, value: GospelVMValue) -> GospelVMResult<usize> {
        if let GospelVMValue::TypeReference(type_index) = value {
           Ok(type_index)
        } else {
            Err(vm_error!(Some(self), "Expected a type reference, got value of type {}", value.value_type()))
        }
    }
    fn unwrap_value_as_base_type_index_checked(&self, value: GospelVMValue, run_context: &GospelVMRunContext) -> GospelVMResult<usize> {
        let type_index = self.unwrap_value_as_type_index_checked(value)?;
        if let Type::CVQualified(cv_qualified_type) = run_context.type_by_index(type_index) {
            Ok(cv_qualified_type.base_type_index)
        } else { Ok(type_index) }
    }
    fn validate_struct_instance_template(&self, instance: &GospelVMStruct, template: &Rc<GospelVMStructTemplate>) -> GospelVMResult<()> {
        if !Rc::ptr_eq(&instance.template, template) {
            vm_bail!(Some(self), "Expected a struct value of type {}, got struct value of type {}",
                template.struct_name().unwrap_or("<unnamed>"), instance.template.struct_name().unwrap_or("<unnamed>"));
        }
        Ok({})
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

    fn run(state: &mut GospelVMExecutionState, run_context: &mut GospelVMRunContext) -> GospelVMResult<()> {
        // Reset counters for the current stack frame
        state.current_instruction_index = 0;
        state.current_loop_jump_count = 0;

        loop {
            // Enter the VM from the current position
            let inner_run_result = Self::run_inner(state, run_context);

            // If there was an exception, and we have an exception handler stack entry, attempt VM re-entry from the exception handler
            if inner_run_result.is_err() && !state.exception_handler_stack.is_empty() {
                let exception_handler = state.exception_handler_stack.pop().unwrap();

                state.stack = exception_handler.start_stack_snapshot;
                state.jump_control_flow_checked(exception_handler.target_instruction_index)?;
                continue;
            }
            // There is no exception handler. Just return the result and check that the function has actually written return value
            inner_run_result?;
            if state.return_value_slot.borrow().is_none() {
                vm_bail!(Some(&state), "Function did not return a value");
            }
            return Ok({});
        }
    }
    fn run_inner(state: &mut GospelVMExecutionState, run_context: &mut GospelVMRunContext) -> GospelVMResult<()> {
        // Main VM loop
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
                GospelOpcode::SetReturnValue => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    if stack_value.value_type() != state.function_definition.return_value_type {
                        vm_bail!(Some(&state), "Incompatible return value type");
                    }
                    if !state.stack.is_empty() {
                        vm_bail!(Some(&state), "Stack not empty upon function return");
                    }
                    if state.return_value_slot.borrow().is_some() {
                        vm_bail!(Some(&state), "Function return value written multiple times; function can only return value once");
                    }
                    *state.return_value_slot.borrow_mut() = Some(stack_value);
                }
                GospelOpcode::Call => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut function_arguments: Vec<GospelVMValue> = vec![GospelVMValue::Integer(0); number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow()?;
                        function_arguments[number_of_arguments - index - 1] = argument_value;
                    }
                    let closure = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_closure_checked(x))?;
                    if state.recursion_counter >= state.max_recursion_depth {
                        vm_bail!(Some(&state), "Recursion limit reached");
                    }
                    let return_value = closure.execute_internal(function_arguments, run_context, Some(&state))?;
                    state.push_stack_check_overflow(return_value)?;
                }
                GospelOpcode::BindClosure => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut closure_arguments: Vec<GospelVMValue> = vec![GospelVMValue::Integer(0); number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow()?;
                        closure_arguments[number_of_arguments - index - 1] = argument_value;
                    }
                    let mut closure = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_closure_checked(x))?;
                    closure.arguments.append(&mut closure_arguments);
                    if closure.arguments.len() >= state.max_stack_size {
                        vm_bail!(Some(&state), "Closure captured argument number limit reached");
                    }
                    state.push_stack_check_overflow(GospelVMValue::Closure(closure))?;
                }
                GospelOpcode::RaiseException => {
                    let message_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let message = state.get_referenced_string_checked(message_index)?;
                    vm_bail!(Some(&state), "User exception: {}", message);
                }
                GospelOpcode::Typeof => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let result = stack_value.value_type() as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::Return => {
                    // Return unconditionally breaks from the instruction loop
                    break;
                }
                GospelOpcode::PushExceptionHandler => {
                    let start_instruction_index = state.current_instruction_index;
                    let target_instruction_index = state.immediate_value_checked(instruction, 0)? as usize;

                    if state.exception_handler_stack.len() > state.max_exception_handler_depth {
                        vm_bail!(Some(state), "Exception handler stack limit reached");
                    }
                    let start_stack_snapshot = state.stack.clone();
                    state.exception_handler_stack.push(GospelExceptionHandler{
                        start_instruction_index,
                        start_stack_snapshot,
                        target_instruction_index,
                    });
                }
                GospelOpcode::PopExceptionHandler => {
                    if state.exception_handler_stack.is_empty() {
                        vm_bail!(Some(state), "Exception handler stack underflow");
                    }
                    state.exception_handler_stack.pop();
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
                GospelOpcode::LoadArgumentValue => {
                    let argument_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let argument_value = state.copy_argument_value_checked(argument_index)?;
                    state.push_stack_check_overflow(argument_value)?;
                }
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
                GospelOpcode::LoadTargetProperty => {
                    let target_property_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let target_property_name = state.get_referenced_string_checked(target_property_name_index)?;

                    let target_property = GospelTargetProperty::from_str(target_property_name)
                        .map_err(|x| vm_error!(Some(&state), "Unknown target property {}: {}", target_property_name, x))?;
                    let result_value = if let Some(target_triplet) = run_context.target_triplet() {
                        target_property.resolve(target_triplet)
                    } else { vm_bail!(Some(&state), "Target triplet not set to read target property {}", target_property_name); };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result_value))?;
                }
                GospelOpcode::LoadGlobalVariable => {
                    let global_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let global_name = state.get_referenced_string_checked(global_name_index)?;

                    let default_global_value = state.owner_container.global_storage.find_default_global_value(global_name);
                    let result_value = run_context.read_global_value(global_name, default_global_value)
                        .ok_or_else(|| vm_error!(Some(&state), "Global variable {} is not defined and does not have a default value", global_name))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result_value))?;
                }
                GospelOpcode::LoadFunctionClosure => {
                    let function_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let result_value = state.get_referenced_function_checked(function_index)?;
                    state.push_stack_check_overflow(GospelVMValue::Closure(result_value))?;
                }
                // Type creation opcodes
                GospelOpcode::TypeAddConstantQualifier => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let result_type = if let Type::CVQualified(cv_qualified_type) = &run_context.type_by_index(type_index) {
                        CVQualifiedType{base_type_index: cv_qualified_type.base_type_index, constant: true, volatile: cv_qualified_type.volatile}
                    } else {
                        CVQualifiedType{base_type_index: type_index, constant: true, volatile: false}
                    };
                    let result_type_index = run_context.store_type(Type::CVQualified(result_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeAddVolatileQualifier => {
                    let base_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let result_type = if let Type::CVQualified(cv_qualified_type) = &run_context.type_by_index(base_type_index) {
                        CVQualifiedType{base_type_index: cv_qualified_type.base_type_index, constant: cv_qualified_type.constant, volatile: true}
                    } else {
                        CVQualifiedType{base_type_index, constant: false, volatile: true}
                    };
                    let result_type_index = run_context.store_type(Type::CVQualified(result_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypePrimitiveCreate => {
                    let primitive_type_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let primitive_type_name = state.get_referenced_string_checked(primitive_type_name_index)?;

                    let primitive_type = PrimitiveType::from_str(&primitive_type_name)
                        .map_err(|x| vm_error!(Some(&state), "Unknown primitive type name: {} ({})", primitive_type_name, x))?;
                    let result_type_index = run_context.store_type(Type::Primitive(primitive_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypePointerCreate => {
                    let pointee_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let pointer_type = PointerType{pointee_type_index, is_reference: false};
                    let result_type_index = run_context.store_type(Type::Pointer(pointer_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypePointerCreateReference => {
                    let pointee_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let pointer_type = PointerType{pointee_type_index, is_reference: true};
                    let result_type_index = run_context.store_type(Type::Pointer(pointer_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeArrayCreate => {
                    let array_length = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let element_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;

                    let array_type = ArrayType{element_type_index, array_length};
                    let result_type_index = run_context.store_type(Type::Array(array_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeFunctionCreateGlobal => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut argument_type_indices: Vec<usize> = vec![0; number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                        argument_type_indices[number_of_arguments - index - 1] = argument_value;
                    }
                    let return_value_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;

                    let function_type = FunctionType{return_value_type_index, argument_type_indices, this_type_index: None};
                    let result_type_index = run_context.store_type(Type::Function(function_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeFunctionCreateMember => {
                    let number_of_arguments = state.immediate_value_checked(instruction, 0)? as usize;
                    let mut argument_type_indices: Vec<usize> = vec![0; number_of_arguments];
                    for index in 0..number_of_arguments {
                        let argument_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                        argument_type_indices[number_of_arguments - index - 1] = argument_value;
                    }
                    let return_value_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let this_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(this_type_index, run_context)?;

                    let function_type = FunctionType{return_value_type_index, argument_type_indices, this_type_index: Some(this_type_index)};
                    let result_type_index = run_context.store_type(Type::Function(function_type));
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeUDTAllocate => {
                    let type_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let type_name = if type_name_index == -1 { None } else { Some(state.get_referenced_string_checked(type_name_index as usize)?.to_string()) };

                    let type_kind_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let type_kind = UserDefinedTypeKind::from_str(state.get_referenced_string_checked(type_kind_index)?)
                        .map_err(|x| vm_error!(Some(&state), "Unknown UDT kind name: {}", x.to_string()))?;

                    let user_defined_type = UserDefinedType{kind: type_kind, name: type_name, ..UserDefinedType::default()};
                    let result_type_index = run_context.store_unique_named_type(Type::UDT(user_defined_type), state.stack_frame_token);
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeUDTSetUserAlignment => {
                    let user_type_alignment = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    if let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        user_defined_type.user_alignment = Some(max(user_defined_type.user_alignment.unwrap_or(1), user_type_alignment));
                    }
                }
                GospelOpcode::TypeUDTSetMemberPackAlignment => {
                    let member_pack_alignment = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    if let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        user_defined_type.member_pack_alignment = Some(member_pack_alignment);
                    }
                }
                GospelOpcode::TypeUDTAddBaseClass => {
                    // Base class must be complete by the time it is added to this class
                    let base_class_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(base_class_type_index, run_context)?;

                    let field_flags = state.immediate_value_checked(instruction, 0)?;
                    let is_base_class_prototype = field_flags & (1 << 2) != 0;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    if let Some(prototype_base_classes) = run_context.types[type_index].base_class_prototypes.as_mut() {
                        prototype_base_classes.insert(base_class_type_index);
                    }
                    // Only add the base class index to the UDT if this is not a prototype
                    if !is_base_class_prototype && let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        if user_defined_type.kind == UserDefinedTypeKind::Union {
                            vm_bail!(Some(state), "Union types cannot have base classes");
                        }
                        if user_defined_type.base_class_indices.contains(&base_class_type_index) {
                            vm_bail!(Some(state), "Base class #{} specified more than once as a direct base class for type #{}", base_class_type_index, type_index);
                        }
                        user_defined_type.base_class_indices.push(base_class_type_index);
                    }
                }
                GospelOpcode::TypeUDTAddField => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let field_name = if field_name_index == -1 { None } else { Some(state.get_referenced_string_checked(field_name_index as usize)?.to_string()) };

                    let field_flags = state.immediate_value_checked(instruction, 1)?;
                    let is_field_prototype = field_flags & (1 << 2) != 0;

                    let raw_user_alignment = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))?;
                    let user_alignment = if raw_user_alignment == -1 { None } else { Some(raw_user_alignment as usize) };
                    let field_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    let result_field = UserDefinedTypeMember::Field(UserDefinedTypeField{name: field_name.clone(), user_alignment, member_type_index: field_type_index});
                    if let Some(prototype_members) = run_context.types[type_index].member_prototypes.as_mut() {
                        prototype_members.insert(result_field.clone());
                    }
                    // Add field to the actual UDT only if this is not a field prototype
                    if !is_field_prototype && let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        if field_name.is_some() && user_defined_type.members.iter().any(|x| x.name() == field_name.as_deref()) {
                            vm_bail!(Some(state), "Type #{} already contains a member named {}", type_index, field_name.as_ref().unwrap());
                        }
                        user_defined_type.members.push(result_field);
                    }
                }
                GospelOpcode::TypeUDTAddBitfield => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let field_name = if field_name_index == -1 { None } else { Some(state.get_referenced_string_checked(field_name_index as usize)?.to_string()) };

                    let bitfield_flags = state.immediate_value_checked(instruction, 1)?;
                    let is_bitfield_prototype = bitfield_flags & (1 << 2) != 0;

                    let bitfield_width = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;

                    // Bitfield must be of a primitive type
                    let field_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let primitive_field_type = if let Type::Primitive(primitive_type) = &run_context.type_by_index(field_type_index) {
                        primitive_type.clone()
                    } else {
                        vm_bail!(Some(state), "Bitfields can only be created from primitive types, type #{} is not a primitive type", field_type_index);
                    };

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    let result_bitfield = UserDefinedTypeMember::Bitfield(UserDefinedTypeBitfield{name: field_name.clone(), primitive_type: primitive_field_type, bitfield_width});
                    if let Some(prototype_members) = run_context.types[type_index].member_prototypes.as_mut() {
                        prototype_members.insert(result_bitfield.clone());
                    }
                    // Add bitfield to the actual UDT only if this is not a bitfield prototype
                    if !is_bitfield_prototype && let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        if field_name.is_some() && user_defined_type.members.iter().any(|x| x.name() == field_name.as_deref()) {
                            vm_bail!(Some(state), "Type #{} already contains a member named {}", type_index, field_name.as_ref().unwrap());
                        }
                        user_defined_type.members.push(result_bitfield);
                    }
                }
                GospelOpcode::TypeUDTAddVirtualFunction => {
                    let function_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let function_name = state.get_referenced_string_checked(function_name_index as usize)?;

                    let function_flags = state.immediate_value_checked(instruction, 1)?;
                    let is_const_member_function = function_flags & (1 << 0) != 0;
                    let is_function_override = function_flags & (1 << 1) != 0;
                    let is_function_prototype = function_flags & (1 << 2) != 0;

                    let number_of_parameter_stack_values = state.immediate_value_checked(instruction, 2)? as usize;
                    if number_of_parameter_stack_values % 2 != 0 {
                        vm_bail!(Some(state), "Invalid number of parameter stack values for TypeUDTAddVirtualFunction; expected even number of stack parameters (pairs of parameter type and name index)");
                    }

                    let number_of_parameters = number_of_parameter_stack_values / 2;
                    let mut parameters: Vec<FunctionParameterDeclaration> = vec![FunctionParameterDeclaration::default(); number_of_parameters];
                    for index in 0..number_of_parameters {
                        let parameter_name_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))?;
                        let parameter_name = if parameter_name_index == -1 { None } else { Some(state.get_referenced_string_checked(parameter_name_index as usize)?.to_string()) };
                        let parameter_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                        parameters[number_of_parameters - index - 1] = FunctionParameterDeclaration{parameter_type_index, parameter_name};
                    }

                    let return_value_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let new_function_declaration = FunctionDeclaration{name: function_name.to_string(), return_value_type_index, parameters, is_const_member_function, is_virtual_function_override: is_function_override};

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    if let Some(prototype_members) = run_context.types[type_index].member_prototypes.as_mut() {
                        prototype_members.insert(UserDefinedTypeMember::VirtualFunction(new_function_declaration.clone()));
                    }
                    // Add virtual function to the UDT only if this is not a function prototype
                    if !is_function_prototype && let Type::UDT(user_defined_type) = &mut run_context.types[type_index].wrapped_type {
                        if user_defined_type.kind == UserDefinedTypeKind::Union {
                            vm_bail!(Some(state), "Union types cannot have virtual functions");
                        }
                        if user_defined_type.members.iter().any(|x| !matches!(x, UserDefinedTypeMember::VirtualFunction(_)) && x.name() == Some(function_name)) {
                            vm_bail!(Some(state), "Type #{} already contains a member named {}", type_index, function_name);
                        }
                        if user_defined_type.members.iter().any(|x| {
                            if let UserDefinedTypeMember::VirtualFunction(function) = x && x.name() == Some(function_name) &&
                                function.function_signature() == new_function_declaration.function_signature() { true } else { false }
                        }) {
                            vm_bail!(Some(state), "Type #{} already contains a function named {} with identical signature", type_index, function_name);
                        }
                        user_defined_type.members.push(UserDefinedTypeMember::VirtualFunction(new_function_declaration))
                    }
                }
                GospelOpcode::TypeUDTAttachMetadata => {
                    let metadata_struct = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_struct_checked(x))?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    run_context.types[type_index].vm_metadata = Some(metadata_struct);
                }
                GospelOpcode::TypeMarkPartial => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    run_context.types[type_index].partial_type = true;
                }
                GospelOpcode::TypeFinalize => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    // Resetting the stack frame token seals the type and prevents any future modifications to it
                    run_context.types[type_index].owner_stack_frame_token = 0;
                }
                GospelOpcode::TypeEnumAllocate => {
                    let type_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let type_name = if type_name_index == -1 { None } else { Some(state.get_referenced_string_checked(type_name_index as usize)?.to_string()) };

                    let enum_kind_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let enum_kind = EnumKind::from_str(state.get_referenced_string_checked(enum_kind_index)?)
                        .map_err(|x| vm_error!(Some(&state), "Unknown enum kind name: {}", x.to_string()))?;

                    let enum_type = EnumType{kind: enum_kind, name: type_name, ..EnumType::default()};
                    let result_type_index = run_context.store_unique_named_type(Type::Enum(enum_type), state.stack_frame_token);
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeEnumSetUnderlyingType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_enum_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    // Enum underlying type must be a primitive type
                    let underlying_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let underlying_type = if let Type::Primitive(primitive_type) = &run_context.type_by_index(underlying_type_index) && primitive_type.is_integral() {
                        primitive_type.clone()
                    } else {
                        vm_bail!(Some(state), "Enum underlying type can only be an integral primitive type, type #{} is not an integral primitive type", underlying_type_index);
                    };
                    if let Type::Enum(enum_type) = &mut run_context.types[type_index].wrapped_type {
                        enum_type.underlying_type = Some(underlying_type);
                    }
                }
                GospelOpcode::TypeEnumAddConstantWithValue => {
                    let constant_value = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as u64;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_enum_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    let constant_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let constant_name = if constant_name_index == -1 { None } else { Some(state.get_referenced_string_checked(constant_name_index as usize)?.to_string()) };

                    let constant_flags_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let is_constant_prototype = constant_flags_index & (1 << 2) != 0;
                    let is_constant_signed = constant_flags_index & (1 << 3) != 0;

                    if constant_name.is_some() && let Some(constant_prototypes) = &mut run_context.types[type_index].enum_constant_prototypes {
                        constant_prototypes.insert(constant_name.as_ref().unwrap().clone());
                    }
                    if !is_constant_prototype && let Type::Enum(enum_type) = &mut run_context.types[type_index].wrapped_type {
                        enum_type.constants.push(EnumConstant{name: constant_name, value: constant_value, is_signed: is_constant_signed});
                    }
                }
                GospelOpcode::TypeEnumAddConstant => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    state.validate_type_index_enum_type(type_index, run_context)?;
                    state.validate_type_not_finalized(type_index, run_context)?;

                    let constant_name_index = state.immediate_value_checked(instruction, 0)? as i32;
                    let constant_name = if constant_name_index == -1 { None } else { Some(state.get_referenced_string_checked(constant_name_index as usize)?.to_string()) };

                    let constant_flags_index = state.immediate_value_checked(instruction, 1)? as usize;
                    let is_constant_prototype = constant_flags_index & (1 << 2) != 0;

                    if constant_name.is_some() && let Some(constant_prototypes) = &mut run_context.types[type_index].enum_constant_prototypes {
                        constant_prototypes.insert(constant_name.as_ref().unwrap().clone());
                    }
                    if !is_constant_prototype && let Type::Enum(enum_type) = &mut run_context.types[type_index].wrapped_type {
                        let (constant_value, is_constant_signed) = if let Some(last_constant_def) = enum_type.constants.last() {
                            if last_constant_def.is_signed {
                                let last_constant_value = last_constant_def.value as i64;
                                ((last_constant_value + 1) as u64, true)
                            } else { (last_constant_def.value + 1, false) }
                        } else { (0, false) };
                        enum_type.constants.push(EnumConstant{name: constant_name, value: constant_value, is_signed: is_constant_signed});
                    }
                }
                // Type access opcodes
                GospelOpcode::TypeIsSameType => {
                    // We do not retrieve base types here, but compare given types directly -- const A is not the same type as A
                    let type_index_a = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    let type_index_b = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;

                    let result = if type_index_a == type_index_b { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeGetBaseType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(type_index))?;
                }
                GospelOpcode::TypeIsPrimitiveType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::Primitive(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeIsPointerType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::Pointer(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeIsArrayType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::Array(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeIsFunctionType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::Function(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeIsUDTType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::UDT(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeIsEnumType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if matches!(run_context.type_by_index(type_index), Type::Enum(_)) { 1 } else { 0 };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypePointerGetPointeeType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result_type_index = if let Type::Pointer(pointer_type) = run_context.type_by_index(type_index) {
                        pointer_type.pointee_type_index
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a pointer type; cannot retrieve pointee type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypePointerIsReference => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result_value = if let Type::Pointer(pointer_type) = run_context.type_by_index(type_index) {
                        if pointer_type.is_reference { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a pointer type; cannot determine if it is a reference type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result_value))?;
                }
                GospelOpcode::TypeArrayGetElementType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result_type_index = if let Type::Array(array_type) = run_context.type_by_index(type_index) {
                        array_type.element_type_index
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an array type; cannot retrieve element type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeArrayGetLength => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result = if let Type::Array(array_type) = run_context.type_by_index(type_index) {
                        array_type.array_length as i32
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an array type; cannot retrieve length", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTIsBaseClassOf => {
                    let base_type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(base_type_index, run_context)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let result = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        if base_type_index == type_index || user_defined_type.is_child_of(base_type_index, run_context) { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTHasField => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let field_name = state.get_referenced_string_checked(field_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let result = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        let found_field = user_defined_type.find_map_member_by_name(&field_name, &|x| if matches!(x, UserDefinedTypeMember::Field(_)) { Some(x.clone()) } else { None }, run_context);
                        if found_field.is_some() { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTTypeofField => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let field_name = state.get_referenced_string_checked(field_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let result_type_index = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.find_map_member_by_name(&field_name, &|x| if let UserDefinedTypeMember::Field(field) = x { Some(field.member_type_index) } else { None }, run_context)
                            .ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have a field named {}", type_index, field_name))?
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeUDTGetMetadata => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let metadata_struct = run_context.types[type_index].vm_metadata.clone()
                        .ok_or_else(|| vm_error!(Some(&state), "Type layout metadata not set on type layout"))?;
                    state.push_stack_check_overflow(GospelVMValue::Struct(metadata_struct))?;
                }
                GospelOpcode::TypeFunctionIsMemberFunction => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result = if let Type::Function(function_type) = run_context.type_by_index(type_index) {
                        if function_type.this_type_index.is_some() { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a function type; cannot determine whenever it is a member function or not", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeFunctionGetThisType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result_type_index = if let Type::Function(function_type) = run_context.type_by_index(type_index) {
                        if let Some(this_type_index) = function_type.this_type_index { this_type_index } else {
                            vm_bail!(Some(state), "Function Type #{} is not a member function", type_index);
                        }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a function type; cannot retrieve this type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeFunctionGetReturnValueType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result_type_index = if let Type::Function(function_type) = run_context.type_by_index(type_index) {
                        function_type.return_value_type_index
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a function type; cannot retrieve return value type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeFunctionGetArgumentCount => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result = if let Type::Function(function_type) = run_context.type_by_index(type_index) {
                        function_type.argument_type_indices.len() as i32
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a function type; cannot determine argument count", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeFunctionGetArgumentType => {
                    let argument_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_int_checked(x))? as usize;
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;

                    let result_type_index = if let Type::Function(function_type) = run_context.type_by_index(type_index) {
                        if argument_index < function_type.argument_type_indices.len() {
                            function_type.argument_type_indices[argument_index]
                        } else {
                            vm_bail!(Some(state), "Function Type #{} does not have argument at index #{}", type_index, argument_index);
                        }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a function type; cannot determine argument count", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeEnumIsScopedEnum => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if let Type::Enum(enum_type) = run_context.type_by_index(type_index) {
                        if enum_type.kind == EnumKind::Scoped { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an enum type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeEnumGetUnderlyingType => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result_type_index = if let Type::Enum(enum_type) = run_context.type_by_index(type_index) {
                        // If we can calculate underlying type without target triplet, try to do that
                        if let Some(static_underlying_type) = enum_type.underlying_type_no_target_no_constants() {
                            run_context.store_type(Type::Primitive(static_underlying_type))
                        } else if let Some(target_triplet) = run_context.target_triplet() {
                            let target_underlying_type = enum_type.underlying_type(target_triplet).map_err(|x| vm_error!(Some(&state), "Failed to calculate enum underlying type: {}", x))?;
                            run_context.store_type(Type::Primitive(target_underlying_type))
                        } else {
                            vm_bail!(Some(state), "Target triplet not set for implicit unscoped enum underlying type calculation");
                        }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an enum type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::TypeReference(result_type_index))?;
                }
                GospelOpcode::TypeEnumHasConstantByName => {
                    let constant_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let constant_name = state.get_referenced_string_checked(constant_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    let result = if let Type::Enum(enum_type) = run_context.type_by_index(type_index) {
                        if enum_type.constants.iter().any(|x| x.name.as_ref().map(|x| x.as_str()) == Some(constant_name)) { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an enum type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeEnumConstantValueByName => {
                    let constant_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let constant_name = state.get_referenced_string_checked(constant_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    if let Type::Enum(enum_type) = run_context.type_by_index(type_index) {
                        if let Some(constant_def) = enum_type.constants.iter().find(|x| x.name.as_ref().map(|x| x.as_str()) == Some(constant_name)) {
                            // TODO: This truncates the value. Integer should be extended to 64-bit
                            state.push_stack_check_overflow(GospelVMValue::Integer(constant_def.value as i32))?;
                            state.push_stack_check_overflow(GospelVMValue::Integer(if constant_def.is_signed { 1 } else { 0 }))?;
                        } else {
                            vm_bail!(Some(state), "Constant with name {} is not found", constant_name);
                        }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not an enum type", type_index);
                    };
                }
                // Type layout calculation opcodes
                GospelOpcode::TypeCalculateSize => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let result = run_context.type_by_index(type_index).size_and_alignment(run_context, &mut new_type_cache)
                        .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?.0 as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeCalculateAlignment => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_type_index_checked(x))?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let result = run_context.type_by_index(type_index).size_and_alignment(run_context, &mut new_type_cache)
                        .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?.1 as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTCalculateUnalignedSize => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let result = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.layout(run_context, &mut new_type_cache)
                            .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?.unaligned_size as i32
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTHasVTable => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let result = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        if user_defined_type.layout(run_context, &mut new_type_cache)
                            .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?.vtable.is_some() { 1 } else { 0 }
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTCalculateVTableSizeAndOffset => {
                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let vtable = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.layout(run_context, &mut new_type_cache)
                            .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?
                            .vtable.clone().ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have a virtual function table", type_index))?
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(vtable.size as i32))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(vtable.slot_size as i32))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(vtable.offset as i32))?;
                }
                GospelOpcode::TypeUDTCalculateBaseOffset => {
                    let base_class_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(base_class_index, run_context)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let result = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.find_base_class_offset(base_class_index, run_context, &mut new_type_cache)
                            .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?
                            .ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have Type #{} as a Base Class", type_index, base_class_index))? as i32
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                GospelOpcode::TypeUDTCalculateVirtualFunctionOffset => {
                    let function_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let function_name = state.get_referenced_string_checked(function_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let (vtable_offset, function_offset) = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.find_map_member_layout(&function_name, &|ctx| {
                            if let ResolvedUDTMemberLayout::VirtualFunction(virtual_function) = &ctx.owner_layout.member_layouts[ctx.member_index] {
                                Some((ctx.owner_offset + virtual_function.vtable_offset, virtual_function.offset))
                            } else { None }
                        }, run_context, &mut new_type_cache)
                        .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?
                        .ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have a virtual function with name {}", type_index, function_name))?
                    } else {
                        vm_bail!(Some(&state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(function_offset as i32))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(vtable_offset as i32))?;
                }
                GospelOpcode::TypeUDTCalculateFieldOffset => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let field_name = state.get_referenced_string_checked(field_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let field_offset = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.find_map_member_layout(&field_name, &|ctx| {
                            if let ResolvedUDTMemberLayout::Field(field_layout) = &ctx.owner_layout.member_layouts[ctx.member_index] {
                                Some(ctx.owner_offset + field_layout.offset)
                            } else { None }
                        }, run_context, &mut new_type_cache)
                        .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?
                        .ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have a field with name {}", type_index, field_name))?
                    } else {
                        vm_bail!(Some(state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(field_offset as i32))?;
                }
                GospelOpcode::TypeUDTCalculateBitfieldOffsetBitOffsetAndBitWidth => {
                    let field_name_index = state.immediate_value_checked(instruction, 0)? as usize;
                    let field_name = state.get_referenced_string_checked(field_name_index)?;

                    let type_index = state.pop_stack_check_underflow().and_then(|x| state.unwrap_value_as_base_type_index_checked(x, run_context))?;
                    state.validate_type_index_user_defined_type(type_index, run_context)?;
                    run_context.validate_type_not_partial(type_index, Some(state))?;

                    let mut new_type_cache = state.new_type_layout_cache(run_context)?;
                    let (field_offset, field_bit_offset, field_bit_width) = if let Type::UDT(user_defined_type) = run_context.type_by_index(type_index) {
                        user_defined_type.find_map_member_layout(&field_name, &|ctx| {
                            if let ResolvedUDTMemberLayout::Bitfield(bitfield) = &ctx.owner_layout.member_layouts[ctx.member_index] {
                                Some((ctx.owner_offset + bitfield.offset, bitfield.bitfield_offset, bitfield.bitfield_width))
                            } else { None }
                        }, run_context, &mut new_type_cache)
                            .map_err(|x| vm_error!(Some(&state), "Failed to calculate type layout: {}", x))?
                        .ok_or_else(|| vm_error!(Some(&state), "Type #{} does not have a field with name {}", type_index, field_name))?
                    } else {
                        vm_bail!(Some(&state), "Type #{} is not a user defined type", type_index);
                    };
                    state.push_stack_check_overflow(GospelVMValue::Integer(field_bit_width as i32))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(field_bit_offset as i32))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(field_offset as i32))?;
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
                    let struct_field_name = state.get_referenced_string_checked(struct_field_name_index)?;

                    let field_value = struct_value.take_named_property(struct_field_name).with_frame_context(Some(&state))?
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
                    let struct_field_name = state.get_referenced_string_checked(struct_field_name_index)?;

                    struct_value.set_named_property(struct_field_name, Some(field_value)).with_frame_context(Some(&state))?;
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
                    let struct_field_name = state.get_referenced_string_checked(struct_field_name_index)?;

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
                    let struct_field_name = state.get_referenced_string_checked(struct_field_name_index)?;

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
        Ok({})
    }
}

#[derive(Debug)]
pub struct GospelVMContainer {
    container: Rc<GospelContainer>,
    external_references: Vec<Rc<GospelVMContainer>>,
    global_storage: Rc<GospelGlobalStorage>,
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
    fn allocate_new_stack_frame<'a>(self: &'a Rc<Self>, run_context: &mut GospelVMRunContext, function_definition: &'a GospelFunctionDefinition, closure: &'a GospelVMClosure, previous_frame: Option<&'a GospelVMExecutionState>, return_value_slot: &Rc<RefCell<Option<GospelVMValue>>>) -> GospelVMExecutionState<'a> {
        let stack_frame_token = run_context.new_stack_frame_token();
        GospelVMExecutionState{
            owner_container: self,
            function_definition: &function_definition,
            argument_values: &closure.arguments,
            slots: vec![None; function_definition.num_slots as usize],
            referenced_strings: Vec::with_capacity(function_definition.referenced_strings.len()),
            referenced_structs: Vec::with_capacity(function_definition.referenced_structs.len()),
            referenced_functions: Vec::with_capacity(function_definition.referenced_functions.len()),
            stack: Vec::new(),
            exception_handler_stack: Vec::new(),
            current_instruction_index: 0,
            current_loop_jump_count: 0,
            recursion_counter: previous_frame.map(|x| x.recursion_counter).unwrap_or(0),
            return_value_slot: return_value_slot.clone(),
            collapsed_call_chain: RefCell::new(HashSet::new()),
            type_count_at_function_start: run_context.types.len(),
            stack_frame_token,
            previous_frame,
            max_stack_size: 256, // TODO: Make limits configurable
            max_loop_jumps: 8192,
            max_recursion_depth: 128,
            max_exception_handler_depth: 128,
        }
    }
    fn execute_function_cached_internal(self: &Rc<Self>, index: u32, args: &Vec<GospelVMValue>, run_context: &mut GospelVMRunContext, previous_frame: Option<&GospelVMExecutionState>) -> GospelVMResult<GospelVMValue> {
        let key_closure = GospelVMClosure{container: self.clone(), function_index: index, arguments: args.clone()};

        // Check if we have previously called this function with the same argument list
        if let Some(existing_return_value_slot) = run_context.call_result_lookup.get(&key_closure) &&
            let Some(existing_return_value) = existing_return_value_slot.borrow().clone() {
            return Ok(existing_return_value)
        };

        // Retrieve function definition with the given index
        if index as usize >= self.container.functions.len() {
            vm_bail!(previous_frame, "Invalid function index #{} out of bounds (num functions in container: {})", index, self.container.functions.len());
        }
        let return_value_slot = Rc::new(RefCell::new(None));
        let function_definition = &self.container.functions[index as usize];
        let mut new_call_stack_frame = self.allocate_new_stack_frame(run_context, function_definition, &key_closure, previous_frame, &return_value_slot);

        new_call_stack_frame.collapsed_call_chain.borrow_mut().insert(key_closure.clone());
        run_context.call_result_lookup.insert(key_closure.clone(), return_value_slot.clone());
        match self.execute_function_on_stack_frame(run_context, &mut new_call_stack_frame) {
            Ok(_) => {
                // Function call was successful, however we need to copy the information about the call chain to the previous frame so it can be rolled back later if necessary
                if let Some(previous_stack_frame) = previous_frame {
                    let borrowed_call_chain = std::mem::replace(new_call_stack_frame.collapsed_call_chain.borrow_mut().deref_mut(), HashSet::new());
                    previous_stack_frame.collapsed_call_chain.borrow_mut().extend(borrowed_call_chain.into_iter());
                }

                // Function call would not succeed if the function did not return a value, so unwrap here is safe
                Ok(return_value_slot.borrow().clone().unwrap())
            }
            Err(function_call_error) => {
                // Function call resulted in an error. That means we have to roll back cached call results for all functions this function might have called
                for function_call_chain_entry in new_call_stack_frame.collapsed_call_chain.borrow().iter() {
                    run_context.call_result_lookup.remove(function_call_chain_entry);
                }

                // Now that there can be no references to the types created by this function call hierarchy, we can purge all of these types
                let invalidated_type_range = new_call_stack_frame.type_count_at_function_start..run_context.types.len();
                for type_index in invalidated_type_range.clone() {
                    run_context.simple_type_lookup.remove(&run_context.types[type_index].wrapped_type);
                }
                run_context.types.drain(invalidated_type_range);

                // Pass the function call error to the caller now
                Err(function_call_error)
            }
        }
    }
    fn execute_function_on_stack_frame<'a>(self: &'a Rc<Self>, run_context: &mut GospelVMRunContext, stack_frame: &mut GospelVMExecutionState<'a>) -> GospelVMResult<()> {
        // Populate referenced strings
        for string_index in &stack_frame.function_definition.referenced_strings {
            stack_frame.referenced_strings.push(self.container.strings.get(*string_index).with_frame_context(Some(&stack_frame))?);
        }
        // Populate referenced structs
        for struct_index in &stack_frame.function_definition.referenced_structs {
            stack_frame.referenced_structs.push(self.resolve_struct_template(struct_index).with_frame_context(Some(&stack_frame))?);
        }
        // Populate referenced functions
        for function_index in &stack_frame.function_definition.referenced_functions {
            stack_frame.referenced_functions.push(self.resolve_function_index(*function_index).with_frame_context(Some(&stack_frame))?);
        }
        // Run the VM now to calculate the result of the function
        GospelVMExecutionState::run(stack_frame, run_context)?;

        // Successful function execution must always yield a value
        if stack_frame.return_value_slot.borrow().is_none() {
            vm_bail!(Some(&stack_frame), "Function failed to return a value");
        }
        Ok({})
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
#[derive(Debug)]
pub struct GospelVMState {
    containers: Vec<Rc<GospelVMContainer>>,
    containers_by_name: HashMap<String, Rc<GospelVMContainer>>,
    global_storage: Rc<GospelGlobalStorage>,
}
impl GospelVMState {

    /// Creates a new, blank VM state with the provided platform config
    /// Type contains must be mounted to the VM by calling mount_container
    pub fn create() -> Self {
        Self{containers: Vec::new(), containers_by_name: HashMap::new(), global_storage: Rc::new(GospelGlobalStorage::default())}
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
            container: wrapped_container.clone(),
            external_references,
            global_storage: self.global_storage.clone(),
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
            self.global_storage.set_global_default_value(global_name, initial_value)?;
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

    /// Returns a list of modules currently loaded into this VM instance
    pub fn enumerate_modules(&self) -> Vec<Rc<GospelVMContainer>> {
        self.containers.clone()
    }
    /// Returns a container by name
    pub fn find_named_container(&self, name: &str) -> Option<Rc<GospelVMContainer>> {
        self.containers_by_name.get(name).map(|x| x.clone())
    }
    /// Attempts to find a function definition by its fully qualified name (container name combined with function name)
    /// Providing the container context allows resolving local function references as well
    pub fn find_function_by_reference(&self, reference: &GospelSourceObjectReference) -> Option<GospelVMClosure> {
        self.find_named_container(reference.module_name.as_str()).and_then(|container| container.find_named_function(reference.local_name.as_str()))
    }
}
