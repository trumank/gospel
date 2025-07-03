use std::collections::HashMap;
use anyhow::{anyhow, bail};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::{GospelContainer, GospelContainerImport, GospelContainerVersion, GospelGlobalDefinition};
use crate::gospel_type::{GospelExternalTypeReference, GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticTypeInstance, GospelStaticValue, GospelStaticValueType, GospelTypeArgumentDefinition, GospelTypeDefinition, GospelTypeIndex, GospelValueType};

/// Represents a reference to another type
#[derive(Debug, Clone)]
pub enum GospelSourceTypeReference {
    /// a reference to a type in this container
    LocalType{type_name: String},
    /// a reference to a type in another container
    ExternalType{container_name: String, type_name: String},
}

/// Represents a static value
#[derive(Debug, Clone)]
pub enum GospelSourceStaticValue {
    Integer(i32),
    TypeReference(GospelSourceTypeReference),
    StaticTypeInstance(GospelSourceStaticTypeInstance),
}
impl GospelSourceStaticValue {
    pub fn result_value_type(&self) -> GospelValueType {
        match self {
            GospelSourceStaticValue::Integer(_) => { GospelValueType::Integer }
            GospelSourceStaticValue::TypeReference(_) => { GospelValueType::TypeReference }
            GospelSourceStaticValue::StaticTypeInstance(_) => { GospelValueType::TypeLayout }
        }
    }
}

/// Represents a type instance created from type reference and arguments represented as static values
#[derive(Debug, Clone)]
pub struct GospelSourceStaticTypeInstance {
    pub type_reference: GospelSourceTypeReference,
    pub arguments: Vec<GospelSourceStaticValue>,
}

/// Represents a value with which a slot is populated before type layout calculation occurs
#[derive(Debug, Default, Clone)]
pub enum GospelSourceSlotBinding {
    /// slot is not initialized with a value, and must be written to before value can be read from it
    #[default]
    Uninitialized,
    /// slot is initialized with the provided value
    StaticValue(GospelSourceStaticValue),
    /// slot is initialized with the value of the provided platform config property
    PlatformConfigProperty(GospelPlatformConfigProperty),
    /// slot is initialized with the value of a global variable with the specified name
    GlobalVariableValue(String),
    /// slot is initialized with the value of the type argument at the given index
    TypeArgumentValue(u32),
}
impl GospelSourceSlotBinding {
    fn static_value_type(&self) -> Option<GospelValueType> {
        match self {
            GospelSourceSlotBinding::StaticValue(x) => Some(x.result_value_type()),
            GospelSourceSlotBinding::PlatformConfigProperty(_) => Some(GospelValueType::Integer),
            GospelSourceSlotBinding::GlobalVariableValue(_) => Some(GospelValueType::Integer),
            _ => None
        }
    }
}

#[derive(Debug, Clone)]
struct GospelSourceSlotDefinition {
    slot_name: String,
    slot_type: GospelValueType,
    slot_biding: GospelSourceSlotBinding,
}
#[derive(Debug, Clone)]
struct GospelSourceTypeArgument {
    argument_type: GospelValueType,
    default_value: Option<GospelSourceStaticValue>,
}

/// Allows building definitions of types to be added to the type container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceTypeDefinition {
    type_name: String,
    arguments: Vec<GospelSourceTypeArgument>,
    slots: Vec<GospelSourceSlotDefinition>,
    code: Vec<GospelInstruction>,
    referenced_strings: Vec<String>,
    referenced_string_lookup: HashMap<String, u32>,
}
impl GospelSourceTypeDefinition {
    pub fn create(type_name: &str) -> Self {
        Self{
            type_name: type_name.to_string(),
            ..GospelSourceTypeDefinition::default()
        }
    }
    pub fn add_type_argument(&mut self, name: &str, value_type: GospelValueType, default_value: Option<GospelSourceStaticValue>) -> anyhow::Result<u32> {
        if default_value.is_some() && default_value.as_ref().unwrap().result_value_type() != value_type {
            bail!("Default value for type argument {} is of incompatible type", name.to_string());
        }
        let new_argument_index = self.arguments.len() as u32;
        self.arguments.push(GospelSourceTypeArgument{
            argument_type: value_type,
            default_value,
        });
        Ok(new_argument_index)
    }
    pub fn add_slot(&mut self, name: &str, value_type: GospelValueType, binding: GospelSourceSlotBinding) -> anyhow::Result<u32> {
        // Attempt to evaluate the type of the binding with the information we have available (for globals we might not have enough information to do validation here)
        let binding_value_type = match binding {
            GospelSourceSlotBinding::TypeArgumentValue(index) => {
                if index as usize >= self.arguments.len() {
                    bail!("Invalid slot binding to type argument index #{} out of bounds (number of type arguments: {})", index, self.arguments.len());
                }
                Some(self.arguments[index as usize].argument_type)
            }
            _ => binding.static_value_type()
        };
        if binding_value_type.is_some() && binding_value_type.unwrap() != value_type {
            bail!("Slot binding value type is incompatible with the value type of the slot");
        }
        let new_slot_index = self.slots.len() as u32;
        self.slots.push(GospelSourceSlotDefinition{
            slot_name: name.to_string(),
            slot_type: value_type,
            slot_biding: binding,
        });
        Ok(new_slot_index)
    }
    /// Note that this function should generally not be used directly, but is public to make extensions easier
    pub fn add_string_internal(&mut self, string: &str) -> u32 {
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
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[slot_index])))
    }
    pub fn add_int_constant_instruction(&mut self, value: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::IntConstant, &[value as u32])))
    }
    pub fn add_control_flow_instruction(&mut self, opcode: GospelOpcode, target_instruction_index: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::BranchIfNot {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[target_instruction_index])))
    }
    pub fn add_member_instruction(&mut self, opcode: GospelOpcode, member_name: &str) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Member && opcode != GospelOpcode::TypeLayoutDoesMemberExist &&
            opcode != GospelOpcode::TypeLayoutGetMemberOffset && opcode != GospelOpcode::TypeLayoutGetMemberSize &&
            opcode != GospelOpcode::TypeLayoutGetMemberTypeLayout {
            bail!("Invalid opcode for control flow instruction (Member, TypeLayoutDoesMemberExist, TypeLayoutGetMemberOffset, TypeLayoutGetMemberSize and TypeLayoutGetMemberTypeLayout are allowed)");
        }
        let string_index = self.add_string_internal(member_name);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[string_index])))
    }
    pub fn add_variadic_instruction(&mut self, opcode: GospelOpcode, argument_count: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::CreateTypeLayout {
            bail!("Invalid opcode for variadic instruction (CreateTypeLayout is allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[argument_count])))
    }
}

/// Base class used for the creation of type containers
#[derive(Debug, Clone, Default)]
pub struct GospelContainerWriter {
    container: GospelContainer,
    string_lookup: HashMap<String, u32>,
    globals_lookup: HashMap<String, u32>,
    types_lookup: HashMap<String, u32>,
    container_lookup: HashMap<String, u32>,
    import_container_type_lookup: Vec<HashMap<String, u32>>,
    static_type_instance_lookup: HashMap<GospelStaticTypeInstance, u32>,
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
    pub fn define_type(&mut self, source: GospelSourceTypeDefinition) -> anyhow::Result<()> {
        if self.types_lookup.contains_key(source.type_name.as_str()) {
            bail!("Type with name {} is already defined in this container", source.type_name);
        }
        let type_name = self.store_string(source.type_name.as_str());

        let mut arguments: Vec<GospelTypeArgumentDefinition> = Vec::with_capacity(source.arguments.len());
        for argument in &source.arguments {
            let default_value = if argument.default_value.is_some() {
                Some(self.convert_static_value(argument.default_value.as_ref().unwrap())?)
            } else { None };

            arguments.push(GospelTypeArgumentDefinition{
                argument_type: argument.argument_type,
                default_value,
            })
        }

        let mut slots: Vec<GospelSlotDefinition> = Vec::with_capacity(source.slots.len());
        for slot in &source.slots {
            let (binding, binding_data) = self.convert_slot_binding(&slot.slot_biding)?;
            slots.push(GospelSlotDefinition{
                value_type: slot.slot_type,
                binding,
                binding_data,
                debug_name: self.store_string(slot.slot_name.as_str()),
            });
        }

        let referenced_strings: Vec<u32> = source.referenced_strings.iter().map(|x| {
            self.store_string(x.as_str())
        }).collect();

        let type_index = self.container.types.len() as u32;
        let type_name_string = source.type_name.clone();
        self.container.types.push(GospelTypeDefinition{
            type_name, arguments, slots,
            code: source.code,
            referenced_strings,
        });
        self.types_lookup.insert(type_name_string, type_index);
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
    fn convert_slot_binding(&mut self, source: &GospelSourceSlotBinding) -> anyhow::Result<(GospelSlotBinding, GospelStaticValue)> {
        match source {
            GospelSourceSlotBinding::Uninitialized => {
                let value = self.convert_static_value(&GospelSourceStaticValue::Integer(0))?;
                Ok((GospelSlotBinding::Uninitialized, value))
            },
            GospelSourceSlotBinding::StaticValue(source_value) => {
                Ok((GospelSlotBinding::StaticValue, self.convert_static_value(source_value)?))
            },
            GospelSourceSlotBinding::PlatformConfigProperty(property) => {
                let value = self.convert_static_value(&GospelSourceStaticValue::Integer(*property as i32))?;
                Ok((GospelSlotBinding::PlatformConfigProperty, value))
            },
            GospelSourceSlotBinding::GlobalVariableValue(global_variable_name) => {
                let global_variable_index = self.find_or_define_global(global_variable_name.as_str(), None)?;
                let value = self.convert_static_value(&GospelSourceStaticValue::Integer(global_variable_index as i32))?;
                Ok((GospelSlotBinding::GlobalVariableValue, value))
            }
            GospelSourceSlotBinding::TypeArgumentValue(argument_index) => {
                let value = self.convert_static_value(&GospelSourceStaticValue::Integer(*argument_index as i32))?;
                Ok((GospelSlotBinding::TypeArgumentValue, value))
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
    fn find_or_define_external_type(&mut self, container_name: &str, type_name: &str) -> u32 {
        // Resolve the index of the container first
        let container_index = if let Some(existing_container_index) = self.container_lookup.get(container_name) {
            *existing_container_index
        } else {
            let new_container_index = self.container.imports.len() as u32;
            let container_name_index = self.store_string(container_name);

            self.container.imports.push(GospelContainerImport{ container_name: container_name_index });
            self.import_container_type_lookup.push(HashMap::new());
            self.container_lookup.insert(container_name.to_string(), new_container_index);
            new_container_index
        };
        // Referenced container builder cannot be a local variable here because of rust borrowing rules
        if let Some(existing_external_type_index) = self.import_container_type_lookup[container_index as usize].get(type_name) {
            *existing_external_type_index
        } else {
            let new_external_type_index = self.container.external_types.len() as u32;
            let type_name_index = self.store_string(type_name);
            self.container.external_types.push(GospelExternalTypeReference{
                import_index: container_index,
                type_name: type_name_index,
            });
            self.import_container_type_lookup[container_index as usize].insert(type_name.to_string(), new_external_type_index);
            new_external_type_index
        }
    }
    fn find_or_add_static_type_instance(&mut self, type_index: GospelTypeIndex, arguments: Vec<GospelStaticValue>) -> u32 {
        let type_instance = GospelStaticTypeInstance{ type_index, arguments };
        if let Some(existing_type_instance_index) = self.static_type_instance_lookup.get(&type_instance) {
            *existing_type_instance_index
        } else {
            let new_type_instance_index = self.container.static_instances.len() as u32;
            self.container.static_instances.push(type_instance.clone());
            self.static_type_instance_lookup.insert(type_instance, new_type_instance_index);
            new_type_instance_index
        }
    }
    fn convert_type_reference(&mut self, source: &GospelSourceTypeReference) -> anyhow::Result<GospelTypeIndex> {
        match source {
            GospelSourceTypeReference::LocalType{type_name} => {
                self.types_lookup.get(type_name.as_str()).map(|type_index| {
                    GospelTypeIndex::create_local(*type_index)
                }).ok_or_else(|| anyhow!("Failed to find locally defined type {}", type_name.to_string()))
            }
            GospelSourceTypeReference::ExternalType {container_name, type_name} => {
                Ok(GospelTypeIndex::create_external(self.find_or_define_external_type(container_name.as_str(), type_name.as_str())))
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
            GospelSourceStaticValue::TypeReference(type_reference) => {
                Ok(GospelStaticValue{
                    value_type: GospelValueType::TypeReference,
                    static_type: GospelStaticValueType::TypeReference,
                    data: self.convert_type_reference(type_reference)?.raw_value(),
                })
            }
            GospelSourceStaticValue::StaticTypeInstance(type_instance) => {
                let type_id = self.convert_type_reference(&type_instance.type_reference)?;

                let mut arguments: Vec<GospelStaticValue> = Vec::with_capacity(type_instance.arguments.len());
                for argument in &type_instance.arguments {
                    arguments.push(self.convert_static_value(argument)?);
                }
                let type_instance_index = self.find_or_add_static_type_instance(type_id, arguments);
                Ok(GospelStaticValue{
                    value_type: GospelValueType::TypeLayout,
                    static_type: GospelStaticValueType::StaticTypeInstance,
                    data: type_instance_index,
                })
            }
        }
    }
}