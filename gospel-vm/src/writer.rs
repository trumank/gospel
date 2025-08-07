use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use anyhow::{anyhow, bail};
use serde::{Deserialize, Serialize};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::{GospelContainer, GospelContainerImport, GospelContainerVersion, GospelGlobalDefinition};
use crate::gospel_type::{GospelExternalObjectReference, GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelFunctionArgument, GospelFunctionDefinition, GospelObjectIndex, GospelValueType, GospelStructDefinition, GospelFunctionDebugData, GospelStructFieldDefinition};

/// Represents a reference to a function
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct GospelSourceObjectReference {
    pub module_name: String,
    pub local_name: String,
}
impl Display for GospelSourceObjectReference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.module_name, self.local_name)
    }
}

/// Represents a static value
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GospelSourceStaticValue {
    /// signed integer literal
    Integer(i32),
    /// pointer to the function with the provided name
    FunctionId(GospelSourceObjectReference),
    /// value of the provided platform config property
    PlatformConfigProperty(GospelPlatformConfigProperty),
    /// value of a global variable with the specified name
    GlobalVariableValue(String),
}
impl GospelSourceStaticValue {
    pub fn value_type(&self) -> GospelValueType {
        match self {
            GospelSourceStaticValue::Integer(_) => GospelValueType::Integer,
            GospelSourceStaticValue::FunctionId(_) => GospelValueType::Closure,
            GospelSourceStaticValue::PlatformConfigProperty(_) => GospelValueType::Integer,
            GospelSourceStaticValue::GlobalVariableValue(_) => GospelValueType::Integer,
        }
    }
}

/// Definition of a field in a struct
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GospelSourceStructField {
    pub field_name: Option<String>,
    pub field_type: GospelValueType,
}

/// Definition of a named struct potentially local to the module
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GospelSourceStructDefinition {
    pub name: GospelSourceObjectReference,
    pub exported: bool,
    pub fields: Vec<GospelSourceStructField>,
}

/// Represents a value with which a slot is populated before type layout calculation occurs
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GospelSourceSlotBinding {
    /// slot is not initialized with a value, and must be written to before value can be read from it
    #[default]
    Uninitialized,
    /// slot is initialized with the provided value
    StaticValue(GospelSourceStaticValue),
    /// slot is initialized with the value of the function argument at the given index
    ArgumentValue(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct GospelSourceSlotDefinition {
    slot_type: GospelValueType,
    slot_biding: GospelSourceSlotBinding,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelSourceFunctionArgument {
    pub argument_type: GospelValueType,
}

/// Allows building declarations of functions to be added to the container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceFunctionDeclaration {
    pub function_name: GospelSourceObjectReference,
    pub exported: bool,
    pub arguments: Vec<GospelSourceFunctionArgument>,
    pub return_value_type: Option<GospelValueType>,
    pub source_file_name: String,
}
impl PartialEq for GospelSourceFunctionDeclaration {
    fn eq(&self, other: &Self) -> bool {
        self.arguments == other.arguments && self.return_value_type == other.return_value_type
    }
}
impl Eq for GospelSourceFunctionDeclaration {}
impl GospelSourceFunctionDeclaration {
    /// Creates a function declaration. When exported is false, the function will not be visible outside the current container by name
    pub fn create(function_name: GospelSourceObjectReference, exported: bool, source_file_name: String) -> Self {
        Self{
            function_name,
            exported,
            source_file_name,
            ..GospelSourceFunctionDeclaration::default()
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
    pub fn add_function_argument(&mut self, value_type: GospelValueType) -> anyhow::Result<u32> {
        let new_argument_index = self.arguments.len() as u32;
        self.arguments.push(GospelSourceFunctionArgument {
            argument_type: value_type,
        });
        Ok(new_argument_index)
    }
}

/// Represents a fixup that needs to be applied to the control flow instruction
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GospelJumpLabelFixup {
    instruction_index: u32,
    operand_index: u32,
}

/// Allows building definitions of functions to be added to the container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceFunctionDefinition {
    pub declaration: GospelSourceFunctionDeclaration,
    slots: Vec<GospelSourceSlotDefinition>,
    code: Vec<GospelInstruction>,
    referenced_strings: Vec<String>,
    referenced_structs: Vec<GospelSourceObjectReference>,
    referenced_string_lookup: HashMap<String, u32>,
    referenced_structs_lookup: HashMap<GospelSourceObjectReference, u32>,
    debug_instruction_line_numbers: Vec<i32>,
}
impl GospelSourceFunctionDefinition {
    /// Creates a named function from a declaration
    pub fn create(declaration: GospelSourceFunctionDeclaration) -> Self {
        Self{
            declaration,
            ..GospelSourceFunctionDefinition::default()
        }
    }
    pub fn add_slot(&mut self, value_type: GospelValueType, binding: GospelSourceSlotBinding) -> anyhow::Result<u32> {
        if let GospelSourceSlotBinding::StaticValue(static_value) = &binding {
            if static_value.value_type() != value_type {
                bail!("Incompatible static value binding type for slot definition");
            }
        }
        if let GospelSourceSlotBinding::ArgumentValue(argument_index) = &binding {
            if *argument_index as usize >= self.declaration.arguments.len() {
                bail!("Invalid argument index #{} out of bounds (number of function arguments: {})", argument_index, self.declaration.arguments.len());
            }
            if self.declaration.arguments[*argument_index as usize].argument_type != value_type {
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
    /// Note that this function should generally not be used directly, but is public to make extensions easier
    pub fn add_struct_reference_internal(&mut self, struct_reference: GospelSourceObjectReference) -> u32 {
        if let Some(existing_index) = self.referenced_structs_lookup.get(&struct_reference) {
            return *existing_index
        }
        let new_struct_index = self.referenced_structs.len() as u32;
        self.referenced_structs.push(struct_reference.clone());
        self.referenced_structs_lookup.insert(struct_reference, new_struct_index);
        new_struct_index
    }
    /// Returns the number of instructions currently in the function body
    pub fn current_instruction_count(&self) -> u32 {
        self.code.len() as u32
    }
    /// Note that this function should generally not be used, and other forms of add_X_instruction should be used instead
    pub fn add_instruction_internal(&mut self, instruction: GospelInstruction, line_number: i32) -> u32 {
        let new_instruction_index = self.code.len() as u32;
        self.code.push(instruction);
        self.debug_instruction_line_numbers.push(line_number);
        new_instruction_index
    }
    pub fn add_simple_instruction(&mut self, instruction: GospelOpcode, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(instruction, &[])?, line_number))
    }
    pub fn add_slot_instruction(&mut self, opcode: GospelOpcode, slot_index: u32, line_number: i32) -> anyhow::Result<u32> {
        if slot_index as usize >= self.slots.len() {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", slot_index, self.slots.len());
        }
        if opcode != GospelOpcode::LoadSlot && opcode != GospelOpcode::StoreSlot && opcode != GospelOpcode::TakeSlot {
            bail!("Invalid opcode for slot instruction (LoadSlot, StoreSlot and TakeSlot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[slot_index])?, line_number))
    }
    pub fn add_int_constant_instruction(&mut self, value: i32, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::IntConstant, &[value as u32])?, line_number))
    }
    pub fn add_control_flow_instruction_no_fixup(&mut self, opcode: GospelOpcode, target_instruction_index: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::Branchz {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[target_instruction_index])?, line_number))
    }
    pub fn add_control_flow_instruction(&mut self, opcode: GospelOpcode, line_number: i32) -> anyhow::Result<(u32, GospelJumpLabelFixup)> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::Branchz {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        let jump_instruction = self.add_instruction_internal(GospelInstruction::create(opcode, &[u32::MAX])?, line_number);
        Ok((jump_instruction, GospelJumpLabelFixup{instruction_index: jump_instruction, operand_index: 0}))
    }
    pub fn fixup_control_flow_instruction(&mut self, fixup: GospelJumpLabelFixup, target_instruction_index: u32) -> anyhow::Result<()> {
        if fixup.instruction_index as usize >= self.code.len() {
            bail!("Invalid fixup instruction index #{} out of bounds", fixup.instruction_index);
        }
        self.code[fixup.instruction_index as usize].set_immediate_operand(fixup.operand_index as usize, target_instruction_index)
    }
    pub fn add_string_instruction(&mut self, opcode: GospelOpcode, string: &str, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeLayoutDefineMember && opcode != GospelOpcode::TypeLayoutDoesMemberExist &&
            opcode != GospelOpcode::TypeLayoutGetMemberOffset && opcode != GospelOpcode::TypeLayoutGetMemberSize &&
            opcode != GospelOpcode::TypeLayoutGetMemberTypeLayout && opcode != GospelOpcode::TypeLayoutAllocate &&
            opcode != GospelOpcode::Abort {
            bail!("Invalid opcode for named instruction (TypeLayoutAllocate, TypeLayoutDefineMember, TypeLayoutDoesMemberExist, TypeLayoutGetMemberOffset, TypeLayoutGetMemberSize, TypeLayoutGetMemberTypeLayout and Abort are allowed)");
        }
        let string_index = self.add_string_reference_internal(string);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[string_index])?, line_number))
    }
    pub fn add_struct_instruction(&mut self, opcode: GospelOpcode, struct_reference: GospelSourceObjectReference, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructAllocate && opcode != GospelOpcode::StructIsStructOfType {
            bail!("Invalid opcode for typed member access instruction (expected StructAllocate or StructIsStructOfType)");
        }
        let struct_index = self.add_struct_reference_internal(struct_reference);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[struct_index])?, line_number))
    }
    pub fn add_struct_local_member_access_instruction(&mut self, opcode: GospelOpcode, struct_reference: GospelSourceObjectReference, field_index: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructGetLocalField && opcode != GospelOpcode::StructSetLocalField {
            bail!("Invalid opcode for typed member access instruction (expected StructGetNamedTypedField or StructSetNamedTypedField)");
        }
        let struct_index = self.add_struct_reference_internal(struct_reference);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[struct_index, field_index])?, line_number))
    }
    pub fn add_typed_member_access_instruction(&mut self, opcode: GospelOpcode, field_name: &str, field_type: GospelValueType, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructGetNamedTypedField && opcode != GospelOpcode::StructSetNamedTypedField {
            bail!("Invalid opcode for typed member access instruction (expected StructGetNamedTypedField or StructSetNamedTypedField)");
        }
        let field_type_value = field_type as u32;
        let member_name_index = self.add_string_reference_internal(field_name);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[field_type_value, member_name_index])?, line_number))
    }
    pub fn add_variadic_instruction(&mut self, opcode: GospelOpcode, argument_count: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Call && opcode != GospelOpcode::BindClosure {
            bail!("Invalid opcode for variadic instruction (only Call is allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[argument_count])?, line_number))
    }
}

/// Generic sink for building gospel modules (into containers or reference containers)
pub trait GospelModuleVisitor : Debug {
    fn module_name(&self) -> Option<String>;
    fn declare_global(&mut self, name: &str) -> anyhow::Result<()>;
    fn define_global(&mut self, name: &str, value: i32) -> anyhow::Result<()>;
    fn declare_function(&mut self, source: GospelSourceFunctionDeclaration) -> anyhow::Result<()>;
    fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()>;
    fn define_struct(&mut self, source: GospelSourceStructDefinition) -> anyhow::Result<()>;
}

/// Implemented by all module visitors that build the containers
pub trait GospelContainerBuilder {
    fn build(&mut self) -> anyhow::Result<GospelContainer>;
}

/// Implementation of visitor that produces GospelContainers
#[derive(Debug, Clone, Default)]
pub struct GospelContainerWriter {
    container: GospelContainer,
    container_name: String,
    string_lookup: HashMap<String, u32>,
    globals_lookup: HashMap<String, u32>,
    function_lookup: HashMap<String, u32>,
    container_lookup: HashMap<String, u32>,
    import_container_function_lookup: Vec<HashMap<String, u32>>,
    struct_lookup: HashMap<String, u32>,
    import_container_struct_lookup: Vec<HashMap<String, u32>>,
    pending_function_declarations: HashSet<u32>,
    function_signatures: HashMap<u32, GospelSourceFunctionDeclaration>,
}
impl GospelContainerWriter {
    /// Creates a new container writer for the container with the given name
    pub fn create(container_name: &str) -> Self {
        let mut writer = Self::default();
        writer.container_name = container_name.to_string();
        writer.container.header.container_name = writer.store_string(container_name);
        writer.container.header.version = GospelContainerVersion::current_version();
        writer
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
                    value_type, binding: GospelSlotBinding::Uninitialized,
                })
            },
            GospelSourceSlotBinding::StaticValue(source_value) => {
                let static_value = self.convert_static_value(source_value)?;
                Ok(GospelSlotDefinition{
                    value_type, binding: GospelSlotBinding::StaticValue(static_value),
                })
            },
            GospelSourceSlotBinding::ArgumentValue(argument_index) => {
                Ok(GospelSlotDefinition{
                    value_type, binding: GospelSlotBinding::ArgumentValue(*argument_index),
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
    fn find_or_define_container_import(&mut self, container_name: &str) -> u32 {
        if let Some(existing_container_index) = self.container_lookup.get(container_name) {
            *existing_container_index
        } else {
            let new_container_index = self.container.imports.len() as u32;
            let container_name_index = self.store_string(container_name);

            self.container.imports.push(GospelContainerImport{ container_name: container_name_index });
            self.import_container_function_lookup.push(HashMap::new());
            self.container_lookup.insert(container_name.to_string(), new_container_index);
            new_container_index
        }
    }
    fn find_or_define_external_function(&mut self, container_name: &str, function_name: &str) -> u32 {
        // Resolve the index of the container first
        let container_index = self.find_or_define_container_import(container_name);

        // Referenced container builder cannot be a local variable here because of rust borrowing rules
        if let Some(existing_external_function_index) = self.import_container_function_lookup[container_index as usize].get(function_name) {
            *existing_external_function_index
        } else {
            let new_external_function_index = self.container.external_functions.len() as u32;
            let function_name_index = self.store_string(function_name);
            self.container.external_functions.push(GospelExternalObjectReference {
                import_index: container_index,
                object_name: function_name_index,
            });
            self.import_container_function_lookup[container_index as usize].insert(function_name.to_string(), new_external_function_index);
            new_external_function_index
        }
    }
    fn find_locally_defined_function_index(&self, function_name: &str) -> anyhow::Result<GospelObjectIndex> {
        self.function_lookup.get(function_name).map(|function_index| {
            GospelObjectIndex::Local(*function_index)
        }).ok_or_else(|| anyhow!("Failed to find locally defined function {}", function_name.to_string()))
    }
    fn convert_function_reference(&mut self, source: &GospelSourceObjectReference) -> anyhow::Result<GospelObjectIndex> {
        if source.module_name == self.container_name {
            self.find_locally_defined_function_index(source.local_name.as_str())
        } else {
            Ok(GospelObjectIndex::External(self.find_or_define_external_function(source.module_name.as_str(), source.local_name.as_str())))
        }
    }
    fn convert_static_value(&mut self, source: &GospelSourceStaticValue) -> anyhow::Result<GospelStaticValue> {
        match source {
            GospelSourceStaticValue::Integer(integer_value) => {
                Ok(GospelStaticValue::Integer(*integer_value))
            }
            GospelSourceStaticValue::FunctionId(type_reference) => {
                Ok(GospelStaticValue::FunctionIndex(self.convert_function_reference(type_reference)?))
            }
            GospelSourceStaticValue::PlatformConfigProperty(property) => {
                Ok(GospelStaticValue::PlatformConfigProperty(*property))
            },
            GospelSourceStaticValue::GlobalVariableValue(global_variable_name) => {
                let global_variable_index = self.find_or_define_global(global_variable_name.as_str(), None)?;
                Ok(GospelStaticValue::GlobalVariableValue(global_variable_index))
            }
        }
    }
    fn find_locally_defined_struct_index(&self, struct_name: &str) -> anyhow::Result<GospelObjectIndex> {
        self.struct_lookup.get(struct_name).map(|struct_index| {
            GospelObjectIndex::Local(*struct_index)
        }).ok_or_else(|| anyhow!("Failed to find locally defined struct {}", struct_name.to_string()))
    }
    fn find_or_define_external_struct(&mut self, container_name: &str, struct_name: &str) -> u32 {
        let container_index = self.find_or_define_container_import(container_name);

        if let Some(existing_external_struct_index) = self.import_container_struct_lookup[container_index as usize].get(struct_name) {
            *existing_external_struct_index
        } else {
            let new_external_struct_index = self.container.external_structs.len() as u32;
            let struct_name_index = self.store_string(struct_name);
            self.container.external_structs.push(GospelExternalObjectReference {
                import_index: container_index,
                object_name: struct_name_index,
            });
            self.import_container_struct_lookup[container_index as usize].insert(struct_name.to_string(), new_external_struct_index);
            new_external_struct_index
        }
    }
    fn convert_struct_reference(&mut self, source: &GospelSourceObjectReference) -> anyhow::Result<GospelObjectIndex> {
        if source.module_name == self.container_name {
            self.find_locally_defined_struct_index(source.local_name.as_str())
        } else {
            Ok(GospelObjectIndex::External(self.find_or_define_external_struct(source.module_name.as_str(), source.local_name.as_str())))
        }
    }
}
impl GospelModuleVisitor for GospelContainerWriter {
    fn module_name(&self) -> Option<String> {
        Some(self.container_name.clone())
    }
    fn declare_global(&mut self, name: &str) -> anyhow::Result<()> {
        self.find_or_define_global(name, None).map(|_| {})
    }
    fn define_global(&mut self, name: &str, value: i32) -> anyhow::Result<()> {
        self.find_or_define_global(name, Some(value)).map(|_| {})
    }
    fn declare_function(&mut self, source: GospelSourceFunctionDeclaration) -> anyhow::Result<()> {
        if source.function_name.module_name != self.container_name {
            return Ok({})
        }
        if source.return_value_type.is_none() {
            bail!("Function does not have a valid return value type; all functions must return a value");
        }
        
        if let Some(declared_or_defined_function_index) = self.function_lookup.get(&source.function_name.local_name) {
            // Function with the same name has already been declared or defined, make sure the signature matches
            let pending_function_declaration = self.function_signatures.get(declared_or_defined_function_index).unwrap();
            if pending_function_declaration != &source {
                bail!("Function with name {} has been pre-declared with conflicting signature (different argument types, argument count, or return value type)", source.function_name.local_name);
            }
        } else {
            // This function has not been declared or defined yet, so declare it now
            let mut arguments: Vec<GospelFunctionArgument> = Vec::with_capacity(source.arguments.len());
            for argument in &source.arguments {
                arguments.push(GospelFunctionArgument {
                    argument_type: argument.argument_type,
                })
            }
            let function_name = self.store_string(source.function_name.local_name.as_str());

            let placeholder_function_definition = GospelFunctionDefinition {
                name: function_name, arguments, slots: Vec::new(), 
                exported: source.exported,
                return_value_type: source.return_value_type.unwrap(),
                code: Vec::new(),
                referenced_strings: Vec::new(),
                referenced_structs: Vec::new(),
                debug_data: None,
            };
            let function_index = self.container.functions.len() as u32;
            self.container.functions.push(placeholder_function_definition);
            self.pending_function_declarations.insert(function_index);

            let function_name_string = source.function_name.local_name.clone();
            self.function_signatures.insert(function_index, source);
            self.function_lookup.insert(function_name_string, function_index);
        }
        Ok({})
    }
    fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        if source.declaration.function_name.module_name != self.container_name {
            return Ok({})
        }
        if source.declaration.return_value_type.is_none() {
            bail!("Function does not have a valid return value type; all functions must return a value");
        }
        let mut arguments: Vec<GospelFunctionArgument> = Vec::with_capacity(source.declaration.arguments.len());
        for argument in &source.declaration.arguments {
            arguments.push(GospelFunctionArgument {
                argument_type: argument.argument_type,
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
        let referenced_structs = source.referenced_structs.iter()
            .map(|x| self.convert_struct_reference(x))
            .collect::<anyhow::Result<Vec<GospelObjectIndex>>>()?;

        let function_name = self.store_string(source.declaration.function_name.local_name.as_str());
        let debug_data = GospelFunctionDebugData{
            source_file_name: self.store_string(source.declaration.source_file_name.as_str()),
            instruction_line_numbers: source.debug_instruction_line_numbers,
        };

        let result_function_definition = GospelFunctionDefinition {
            name: function_name, arguments, slots,
            exported: source.declaration.exported,
            return_value_type: source.declaration.return_value_type.unwrap(),
            code: source.code,
            referenced_strings,
            referenced_structs,
            debug_data: Some(debug_data),
        };

        if let Some(existing_function_index) = self.function_lookup.get(&source.declaration.function_name.local_name) {
            if self.pending_function_declarations.contains(existing_function_index) {
                // There is a pending pre-declaration for this function. Make sure its signature is identical
                let pending_function_declaration = self.function_signatures.get(existing_function_index).unwrap();
                if pending_function_declaration != &source.declaration {
                    bail!("Function with name {} has been pre-declared with conflicting signature (different argument types, argument count, or return value type)", source.declaration.function_name.local_name);
                }
                // Update the function definition now
                self.container.functions[*existing_function_index as usize] = result_function_definition;
            } else {
                // No pending pre-declaration, this is a conflicting definition of a previously defined function
                bail!("Function with name {} is already defined in this container", source.declaration.function_name.local_name);
            }
        } else {
            // No existing function with the same, define the function now
            let function_index = self.container.functions.len() as u32;
            self.container.functions.push(result_function_definition);

            let function_name_string = source.declaration.function_name.local_name.clone();
            self.function_signatures.insert(function_index, source.declaration);
            self.function_lookup.insert(function_name_string, function_index);
        }
        Ok({})
    }
    fn define_struct(&mut self, source: GospelSourceStructDefinition) -> anyhow::Result<()> {
        if source.name.module_name != self.container_name {
            return Ok({})
        }
        if self.struct_lookup.contains_key(source.name.local_name.as_str()) {
            bail!("Struct {} is already defined in this container", source.name.local_name);
        }
        let struct_index = self.container.structs.len() as u32;
        let struct_name = self.store_string(source.name.local_name.as_str());
        let fields = source.fields.iter().enumerate().map(|(index, x)| GospelStructFieldDefinition{
            field_type: x.field_type,
            field_name: self.store_string(&x.field_name.clone().unwrap_or_else(|| format!("<unnamed@{}>", index))),
        }).collect();
        self.container.structs.push(GospelStructDefinition { name: struct_name, exported: source.exported, fields });
        self.struct_lookup.insert(source.name.local_name.clone(), struct_index);
        Ok({})
    }
}
impl GospelContainerBuilder for GospelContainerWriter {
    fn build(&mut self) -> anyhow::Result<GospelContainer> {
        if !self.pending_function_declarations.is_empty() {
            let declared_function_names: Vec<String> = self.pending_function_declarations.iter()
                .map(|function_index| self.container.functions[*function_index as usize].name)
                .map(|function_name_index| self.container.strings.get(function_name_index).unwrap().to_string())
                .collect();
            bail!("Functions {} have been declared, but have not been defined. All declared functions must be defined", declared_function_names.join(", "));
        }
        Ok(std::mem::take(&mut self.container))
    }
}
