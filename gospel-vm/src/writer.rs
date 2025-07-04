use std::collections::HashMap;
use anyhow::{anyhow, bail};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::{GospelContainer, GospelContainerImport, GospelContainerVersion, GospelGlobalDefinition};
use crate::gospel_type::{GospelExternalFunctionReference, GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelStaticValueType, GospelFunctionArgument, GospelFunctionDefinition, GospelFunctionIndex, GospelValueType, GospelLazyValue, GospelFunctionNamePair};

/// Represents a reference to a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GospelSourceFunctionReference {
    /// a reference to a function in this container
    LocalFunction{ function_name: String},
    /// a reference to a function in another container
    ExternalFunction{container_name: String, function_name: String},
}

/// Represents a static value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GospelSourceStaticValue {
    /// signed integer literal
    Integer(i32),
    /// pointer to the function with the provided name
    FunctionId(GospelSourceFunctionReference),
    /// result of the evaluation of function with provided arguments
    LazyValue(GospelSourceLazyValue),
    /// value of the provided platform config property
    PlatformConfigProperty(GospelPlatformConfigProperty),
    /// value of a global variable with the specified name
    GlobalVariableValue(String),
}
impl GospelSourceStaticValue {
    pub fn value_type(&self) -> GospelValueType {
        match self {
            GospelSourceStaticValue::Integer(_) => GospelValueType::Integer,
            GospelSourceStaticValue::FunctionId(_) => GospelValueType::FunctionPointer,
            GospelSourceStaticValue::LazyValue(value) => value.return_value_type,
            GospelSourceStaticValue::PlatformConfigProperty(_) => GospelValueType::Integer,
            GospelSourceStaticValue::GlobalVariableValue(_) => GospelValueType::Integer,
        }
    }
}

/// Represents a lazily evaluated value created by calling the provided function with the given set of arguments
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GospelSourceLazyValue {
    pub function_reference: GospelSourceFunctionReference,
    pub return_value_type: GospelValueType,
    pub arguments: Vec<GospelSourceStaticValue>,
}

/// Represents a value with which a slot is populated before type layout calculation occurs
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum GospelSourceSlotBinding {
    /// slot is not initialized with a value, and must be written to before value can be read from it
    #[default]
    Uninitialized,
    /// slot is initialized with the provided value
    StaticValue(GospelSourceStaticValue),
    /// slot is initialized with the value of the function argument at the given index
    ArgumentValue(u32),
}

#[derive(Debug, Clone)]
struct GospelSourceSlotDefinition {
    slot_type: GospelValueType,
    slot_biding: GospelSourceSlotBinding,
}
#[derive(Debug, Clone)]
struct GospelSourceFunctionArgument {
    argument_type: GospelValueType,
    default_value: Option<GospelSourceStaticValue>,
}

/// Allows building definitions of functions to be added to the container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceFunctionDefinition {
    function_name: String,
    hidden: bool,
    arguments: Vec<GospelSourceFunctionArgument>,
    slots: Vec<GospelSourceSlotDefinition>,
    code: Vec<GospelInstruction>,
    referenced_strings: Vec<String>,
    referenced_string_lookup: HashMap<String, u32>,
    return_value_type: Option<GospelValueType>,
}
impl GospelSourceFunctionDefinition {
    /// Creates a named function. When hidden is true, the function will not be visible outside the current container by name
    pub fn create(function_name: &str, hidden: bool) -> Self {
        Self{
            function_name: function_name.to_string(),
            hidden,
            ..GospelSourceFunctionDefinition::default()
        }
    }
    pub fn set_return_value_type(&mut self, return_value_type: GospelValueType) {
        self.return_value_type = Some(return_value_type);
    }
    pub fn get_argument_type_at_index(&self, index: u32) -> Option<GospelValueType> {
        if (index as usize) < self.arguments.len() {
            Some(self.arguments[index as usize].argument_type)
        } else { None }
    }
    pub fn add_function_argument(&mut self, value_type: GospelValueType, default_value: Option<GospelSourceStaticValue>) -> anyhow::Result<u32> {
        if default_value.is_some() && default_value.as_ref().unwrap().value_type() != value_type {
            bail!("Incompatible default value type for function argument");
        }
        let new_argument_index = self.arguments.len() as u32;
        self.arguments.push(GospelSourceFunctionArgument {
            argument_type: value_type,
            default_value,
        });
        Ok(new_argument_index)
    }
    pub fn add_slot(&mut self, value_type: GospelValueType, binding: GospelSourceSlotBinding) -> anyhow::Result<u32> {
        if let GospelSourceSlotBinding::StaticValue(static_value) = &binding {
            if static_value.value_type() != value_type {
                bail!("Incompatible static value binding type for slot definition");
            }
        }
        if let GospelSourceSlotBinding::ArgumentValue(argument_index) = &binding {
            if *argument_index as usize >= self.arguments.len() {
                bail!("Invalid argument index #{} out of bounds (number of function arguments: {})", argument_index, self.arguments.len());
            }
            if self.arguments[*argument_index as usize].argument_type != value_type {
                bail!("Incompatible argument type at index #{} for slot definition", argument_index);
            }
        }
        let new_slot_index = self.slots.len() as u32;
        self.slots.push(GospelSourceSlotDefinition{
            slot_type: value_type,
            slot_biding: binding,
        });
        Ok(new_slot_index)
    }
    /// Note that this function should generally not be used directly, but is public to make extensions easier
    pub fn add_string_reference_internal(&mut self, string: &str) -> u32 {
        if let Some(existing_index) = self.referenced_string_lookup.get(string) {
            return *existing_index
        }
        let new_string_index = self.referenced_strings.len() as u32;
        self.referenced_strings.push(string.to_string());
        self.referenced_string_lookup.insert(string.to_string(), new_string_index);
        new_string_index
    }
    /// Note that this function should generally not be used, and other forms of add_X_instruction should be used instead
    pub fn add_instruction_internal(&mut self, instruction: GospelInstruction) -> u32 {
        let new_instruction_index = self.code.len() as u32;
        self.code.push(instruction);
        new_instruction_index
    }
    pub fn add_slot_instruction(&mut self, opcode: GospelOpcode, slot_index: u32) -> anyhow::Result<u32> {
        if slot_index as usize >= self.slots.len() {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", slot_index, self.slots.len());
        }
        if opcode != GospelOpcode::LoadSlot && opcode != GospelOpcode::StoreSlot {
            bail!("Invalid opcode for slot instruction (LoadSlot and StoreSlot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[slot_index])?))
    }
    pub fn add_int_constant_instruction(&mut self, value: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::IntConstant, &[value as u32])?))
    }
    pub fn add_control_flow_instruction(&mut self, opcode: GospelOpcode, target_instruction_index: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::BranchIfNot {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[target_instruction_index])?))
    }
    pub fn add_named_instruction(&mut self, opcode: GospelOpcode, member_name: &str) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeLayoutDefineMember && opcode != GospelOpcode::TypeLayoutDoesMemberExist &&
            opcode != GospelOpcode::TypeLayoutGetMemberOffset && opcode != GospelOpcode::TypeLayoutGetMemberSize &&
            opcode != GospelOpcode::TypeLayoutGetMemberTypeLayout && opcode != GospelOpcode::TypeLayoutAllocate {
            bail!("Invalid opcode for named instruction (TypeLayoutAllocate, TypeLayoutDefineMember, TypeLayoutDoesMemberExist, TypeLayoutGetMemberOffset, TypeLayoutGetMemberSize and TypeLayoutGetMemberTypeLayout are allowed)");
        }
        let string_index = self.add_string_reference_internal(member_name);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[string_index])?))
    }
    pub fn add_variadic_instruction(&mut self, opcode: GospelOpcode, argument_count: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Call {
            bail!("Invalid opcode for variadic instruction (only Call is allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[argument_count])?))
    }
}

/// Base class used for the creation of containers
#[derive(Debug, Clone, Default)]
pub struct GospelContainerWriter {
    container: GospelContainer,
    string_lookup: HashMap<String, u32>,
    globals_lookup: HashMap<String, u32>,
    function_lookup: HashMap<String, u32>,
    container_lookup: HashMap<String, u32>,
    import_container_function_lookup: Vec<HashMap<String, u32>>,
    lazy_value_lookup: HashMap<GospelLazyValue, u32>,
}
impl GospelContainerWriter {
    pub fn create(container_name: &str) -> GospelContainerWriter {
        let mut writer = GospelContainerWriter::default();
        writer.container.header.container_name = writer.store_string(container_name);
        writer.container.header.version = GospelContainerVersion::current_version();
        writer
    }
    pub fn define_global(&mut self, name: &str, default_value: Option<i32>) -> anyhow::Result<()> {
        self.find_or_define_global(name, default_value).map(|_| {})
    }
    pub fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        if self.function_lookup.contains_key(source.function_name.as_str()) {
            bail!("Function with name {} is already defined in this container", source.function_name);
        }
        if source.return_value_type.is_none() {
            bail!("Function does not have a valid return value type; all functions must return a value");
        }
        let mut arguments: Vec<GospelFunctionArgument> = Vec::with_capacity(source.arguments.len());
        for argument in &source.arguments {
            let default_value = if argument.default_value.is_some() {
                Some(self.convert_static_value(argument.default_value.as_ref().unwrap())?)
            } else { None };

            arguments.push(GospelFunctionArgument {
                argument_type: argument.argument_type,
                default_value,
            })
        }

        let mut slots: Vec<GospelSlotDefinition> = Vec::with_capacity(source.slots.len());
        for slot in &source.slots {
            let slot_definition = self.convert_slot_binding(slot.slot_type, &slot.slot_biding)?;
            slots.push(slot_definition);
        }
        let referenced_strings: Vec<u32> = source.referenced_strings.iter().map(|x| {
            self.store_string(x.as_str())
        }).collect();

        let function_index = self.container.functions.len() as u32;
        let function_name_string = source.function_name.clone();
        if !source.hidden {
            let function_name = self.store_string(source.function_name.as_str());
            self.container.function_names.push(GospelFunctionNamePair{ function_index, function_name });
        }
        self.container.functions.push(GospelFunctionDefinition {
            arguments, slots,
            return_value_type: source.return_value_type.unwrap(),
            code: source.code,
            referenced_strings,
        });
        self.function_lookup.insert(function_name_string, function_index);
        Ok({})
    }
    pub fn build(self) -> GospelContainer {
        self.container
    }
    fn store_string(&mut self, string: &str) -> u32 {
        if let Some(index) = self.string_lookup.get(string) {
            return *index
        }
        let new_index = self.container.strings.store(string.to_string());
        self.string_lookup.insert(string.to_string(), new_index);
        new_index
    }
    fn convert_slot_binding(&mut self, value_type: GospelValueType, source: &GospelSourceSlotBinding) -> anyhow::Result<GospelSlotDefinition> {
        match source {
            GospelSourceSlotBinding::Uninitialized => {
                Ok(GospelSlotDefinition{
                    value_type, binding: GospelSlotBinding::StaticValue, static_value: None, argument_index: 0,
                })
            },
            GospelSourceSlotBinding::StaticValue(source_value) => {
                let static_value = self.convert_static_value(source_value)?;
                Ok(GospelSlotDefinition{
                    value_type, binding: GospelSlotBinding::StaticValue, static_value: Some(static_value), argument_index: 0,
                })
            },
            GospelSourceSlotBinding::ArgumentValue(argument_index) => {
                Ok(GospelSlotDefinition{
                    value_type, binding: GospelSlotBinding::ArgumentValue, static_value: None, argument_index: *argument_index,
                })
            }
        }
    }
    fn find_or_define_global(&mut self, name: &str, default_value: Option<i32>) -> anyhow::Result<u32> {
        if let Some(existing_global_index) = self.globals_lookup.get(name) {
            let existing_global = &mut self.container.globals[*existing_global_index as usize];
            if existing_global.default_value.is_none() {
                existing_global.default_value = default_value
            } else if default_value.is_some() && existing_global.default_value != default_value {
                bail!("Multiple global definition for global {} using different default value (previously set to {}, now defined as {})",
                    name.to_string(), existing_global.default_value.unwrap(), default_value.unwrap());
            }
            return Ok(*existing_global_index)
        }
        let new_global_index = self.container.globals.len() as u32;
        let name_index = self.store_string(name);
        self.container.globals.push(GospelGlobalDefinition{ name: name_index, default_value });
        self.globals_lookup.insert(name.to_string(), new_global_index);
        Ok(new_global_index)
    }
    fn find_or_define_external_function(&mut self, container_name: &str, function_name: &str) -> u32 {
        // Resolve the index of the container first
        let container_index = if let Some(existing_container_index) = self.container_lookup.get(container_name) {
            *existing_container_index
        } else {
            let new_container_index = self.container.imports.len() as u32;
            let container_name_index = self.store_string(container_name);

            self.container.imports.push(GospelContainerImport{ container_name: container_name_index });
            self.import_container_function_lookup.push(HashMap::new());
            self.container_lookup.insert(container_name.to_string(), new_container_index);
            new_container_index
        };
        // Referenced container builder cannot be a local variable here because of rust borrowing rules
        if let Some(existing_external_function_index) = self.import_container_function_lookup[container_index as usize].get(function_name) {
            *existing_external_function_index
        } else {
            let new_external_function_index = self.container.external_functions.len() as u32;
            let function_name_index = self.store_string(function_name);
            self.container.external_functions.push(GospelExternalFunctionReference {
                import_index: container_index,
                function_name: function_name_index,
            });
            self.import_container_function_lookup[container_index as usize].insert(function_name.to_string(), new_external_function_index);
            new_external_function_index
        }
    }
    fn find_or_add_lazy_value(&mut self, function_index: GospelFunctionIndex, arguments: Vec<GospelStaticValue>) -> u32 {
        let lazy_value = GospelLazyValue{ function_index, arguments };
        if let Some(existing_lazy_value_index) = self.lazy_value_lookup.get(&lazy_value) {
            *existing_lazy_value_index
        } else {
            let new_lazy_value_index = self.container.lazy_values.len() as u32;
            self.container.lazy_values.push(lazy_value.clone());
            self.lazy_value_lookup.insert(lazy_value, new_lazy_value_index);
            new_lazy_value_index
        }
    }
    fn convert_function_reference(&mut self, source: &GospelSourceFunctionReference) -> anyhow::Result<GospelFunctionIndex> {
        match source {
            GospelSourceFunctionReference::LocalFunction {function_name} => {
                self.function_lookup.get(function_name.as_str()).map(|function_index| {
                    GospelFunctionIndex::create_local(*function_index)
                }).ok_or_else(|| anyhow!("Failed to find locally defined function {}", function_name.to_string()))
            }
            GospelSourceFunctionReference::ExternalFunction {container_name, function_name} => {
                Ok(GospelFunctionIndex::create_external(self.find_or_define_external_function(container_name.as_str(), function_name.as_str())))
            }
        }
    }
    fn convert_static_value(&mut self, source: &GospelSourceStaticValue) -> anyhow::Result<GospelStaticValue> {
        match source {
            GospelSourceStaticValue::Integer(integer_value) => {
                Ok(GospelStaticValue{
                    value_type: GospelValueType::Integer,
                    static_type: GospelStaticValueType::Integer,
                    data: *integer_value as u32,
                })
            }
            GospelSourceStaticValue::FunctionId(type_reference) => {
                Ok(GospelStaticValue{
                    value_type: GospelValueType::FunctionPointer,
                    static_type: GospelStaticValueType::FunctionIndex,
                    data: self.convert_function_reference(type_reference)?.raw_value(),
                })
            }
            GospelSourceStaticValue::LazyValue(lazy_value) => {
                let function_index = self.convert_function_reference(&lazy_value.function_reference)?;

                let mut arguments: Vec<GospelStaticValue> = Vec::with_capacity(lazy_value.arguments.len());
                for argument in &lazy_value.arguments {
                    arguments.push(self.convert_static_value(argument)?);
                }
                let lazy_value_index = self.find_or_add_lazy_value(function_index, arguments);
                Ok(GospelStaticValue{
                    value_type: lazy_value.return_value_type,
                    static_type: GospelStaticValueType::LazyValue,
                    data: lazy_value_index,
                })
            }
            GospelSourceStaticValue::PlatformConfigProperty(property) => {
                Ok(GospelStaticValue{
                    value_type: GospelValueType::Integer,
                    static_type: GospelStaticValueType::PlatformConfigProperty,
                    data: *property as u32,
                })
            },
            GospelSourceStaticValue::GlobalVariableValue(global_variable_name) => {
                let global_variable_index = self.find_or_define_global(global_variable_name.as_str(), None)?;
                Ok(GospelStaticValue{
                    value_type: GospelValueType::Integer,
                    static_type: GospelStaticValueType::GlobalVariableValue,
                    data: global_variable_index,
                })
            }
        }
    }
}