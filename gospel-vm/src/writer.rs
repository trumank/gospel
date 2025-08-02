use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use anyhow::{anyhow, bail};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::{GospelContainer, GospelContainerImport, GospelContainerVersion, GospelGlobalDefinition};
use crate::gospel_type::{GospelExternalObjectReference, GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelStaticValueType, GospelFunctionArgument, GospelFunctionDefinition, GospelObjectIndex, GospelValueType, GospelLazyValue, GospelObjectIndexNamePair, GospelStructDefinition, GospelStructNameInfo};

/// Represents a reference to a function
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GospelSourceStaticValue {
    /// signed integer literal
    Integer(i32),
    /// pointer to the function with the provided name
    FunctionId(GospelSourceObjectReference),
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
            GospelSourceStaticValue::FunctionId(_) => GospelValueType::Closure,
            GospelSourceStaticValue::LazyValue(value) => value.return_value_type,
            GospelSourceStaticValue::PlatformConfigProperty(_) => GospelValueType::Integer,
            GospelSourceStaticValue::GlobalVariableValue(_) => GospelValueType::Integer,
        }
    }
}

/// Represents a lazily evaluated value created by calling the provided function with the given set of arguments
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GospelSourceLazyValue {
    pub function_reference: GospelSourceObjectReference,
    pub return_value_type: GospelValueType,
    pub arguments: Vec<GospelSourceStaticValue>,
}

/// Definition of a field in a struct
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GospelSourceStructField {
    pub field_name: Option<String>,
    pub field_type: GospelValueType,
}

/// Definition of a named struct potentially local to the module
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GospelSourceStructDefinition {
    pub name: GospelSourceObjectReference,
    pub hidden: bool,
    pub fields: Vec<GospelSourceStructField>,
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
pub struct GospelSourceFunctionArgument {
    pub argument_type: GospelValueType,
    pub default_value: Option<GospelSourceStaticValue>,
}

/// Allows building declarations of functions to be added to the container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceFunctionDeclaration {
    pub function_name: GospelSourceObjectReference,
    pub hidden: bool,
    pub arguments: Vec<GospelSourceFunctionArgument>,
    pub return_value_type: Option<GospelValueType>,
}
impl GospelSourceFunctionDeclaration {
    /// Creates a function declaration. When hidden is true, the function will not be visible outside the current container by name
    pub fn create(function_name: GospelSourceObjectReference, hidden: bool) -> Self {
        Self{
            function_name: function_name,
            hidden,
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
    pub fn add_instruction_internal(&mut self, instruction: GospelInstruction) -> u32 {
        let new_instruction_index = self.code.len() as u32;
        self.code.push(instruction);
        new_instruction_index
    }
    pub fn add_simple_instruction(&mut self, instruction: GospelOpcode) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(instruction, &[])?))
    }
    pub fn add_slot_instruction(&mut self, opcode: GospelOpcode, slot_index: u32) -> anyhow::Result<u32> {
        if slot_index as usize >= self.slots.len() {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", slot_index, self.slots.len());
        }
        if opcode != GospelOpcode::LoadSlot && opcode != GospelOpcode::StoreSlot && opcode != GospelOpcode::TakeSlot {
            bail!("Invalid opcode for slot instruction (LoadSlot, StoreSlot and TakeSlot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[slot_index])?))
    }
    pub fn add_int_constant_instruction(&mut self, value: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::IntConstant, &[value as u32])?))
    }
    pub fn add_control_flow_instruction_no_fixup(&mut self, opcode: GospelOpcode, target_instruction_index: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::Branchz {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[target_instruction_index])?))
    }
    pub fn add_control_flow_instruction(&mut self, opcode: GospelOpcode) -> anyhow::Result<GospelJumpLabelFixup> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::Branchz {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        let jump_instruction = self.add_instruction_internal(GospelInstruction::create(opcode, &[u32::MAX])?);
        Ok(GospelJumpLabelFixup{instruction_index: jump_instruction, operand_index: 0})
    }
    pub fn fixup_control_flow_instruction(&mut self, fixup: GospelJumpLabelFixup, target_instruction_index: u32) -> anyhow::Result<()> {
        if fixup.instruction_index as usize >= self.code.len() {
            bail!("Invalid fixup instruction index #{} out of bounds", fixup.instruction_index);
        }
        self.code[fixup.instruction_index as usize].set_immediate_operand(fixup.operand_index as usize, target_instruction_index)
    }
    pub fn add_string_instruction(&mut self, opcode: GospelOpcode, string: &str) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeLayoutDefineMember && opcode != GospelOpcode::TypeLayoutDoesMemberExist &&
            opcode != GospelOpcode::TypeLayoutGetMemberOffset && opcode != GospelOpcode::TypeLayoutGetMemberSize &&
            opcode != GospelOpcode::TypeLayoutGetMemberTypeLayout && opcode != GospelOpcode::TypeLayoutAllocate &&
            opcode != GospelOpcode::Abort {
            bail!("Invalid opcode for named instruction (TypeLayoutAllocate, TypeLayoutDefineMember, TypeLayoutDoesMemberExist, TypeLayoutGetMemberOffset, TypeLayoutGetMemberSize, TypeLayoutGetMemberTypeLayout and Abort are allowed)");
        }
        let string_index = self.add_string_reference_internal(string);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[string_index])?))
    }
    pub fn add_struct_instruction(&mut self, opcode: GospelOpcode, struct_reference: GospelSourceObjectReference) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructAllocate && opcode != GospelOpcode::StructIsStructOfType {
            bail!("Invalid opcode for typed member access instruction (expected StructAllocate or StructIsStructOfType)");
        }
        let struct_index = self.add_struct_reference_internal(struct_reference);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[struct_index])?))
    }
    pub fn add_struct_local_member_access_instruction(&mut self, opcode: GospelOpcode, struct_reference: GospelSourceObjectReference, field_index: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructGetLocalField && opcode != GospelOpcode::StructSetLocalField {
            bail!("Invalid opcode for typed member access instruction (expected StructGetNamedTypedField or StructSetNamedTypedField)");
        }
        let struct_index = self.add_struct_reference_internal(struct_reference);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[struct_index, field_index])?))
    }
    pub fn add_typed_member_access_instruction(&mut self, opcode: GospelOpcode, field_name: &str, field_type: GospelValueType) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::StructGetNamedTypedField && opcode != GospelOpcode::StructSetNamedTypedField {
            bail!("Invalid opcode for typed member access instruction (expected StructGetNamedTypedField or StructSetNamedTypedField)");
        }
        let field_type_value = field_type as u32;
        let member_name_index = self.add_string_reference_internal(field_name);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[field_type_value, member_name_index])?))
    }
    pub fn add_variadic_instruction(&mut self, opcode: GospelOpcode, argument_count: u32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Call && opcode != GospelOpcode::BindClosure {
            bail!("Invalid opcode for variadic instruction (only Call is allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[argument_count])?))
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

/// A frontend for plugging multiple container visitors into a single object
#[derive(Debug, Default)]
pub struct GospelMultiContainerVisitor {
    pub visitors: Vec<Rc<RefCell<dyn GospelModuleVisitor>>>,
}
impl GospelMultiContainerVisitor {
    pub fn create() -> Self {
        Self::default()
    }
    pub fn add_visitor(&mut self, visitor: Rc<RefCell<dyn GospelModuleVisitor>>) {
        self.visitors.push(visitor);
    }
}
impl GospelModuleVisitor for GospelMultiContainerVisitor {
    fn module_name(&self) -> Option<String> {
        self.visitors.iter().find_map(|x| x.borrow().module_name())
    }
    fn declare_global(&mut self, name: &str) -> anyhow::Result<()> {
        for visitor in &mut self.visitors {
            visitor.borrow_mut().declare_global(name)?;
        }
        Ok({})
    }
    fn define_global(&mut self, name: &str, value: i32) -> anyhow::Result<()> {
        for visitor in &mut self.visitors {
            visitor.borrow_mut().define_global(name, value)?;
        }
        Ok({})
    }
    fn declare_function(&mut self, source: GospelSourceFunctionDeclaration) -> anyhow::Result<()> {
        for visitor in &mut self.visitors {
            visitor.borrow_mut().declare_function(source.clone())?
        }
        Ok({})
    }
    fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        for visitor in &mut self.visitors {
            visitor.borrow_mut().define_function(source.clone())?
        }
        Ok({})
    }
    fn define_struct(&mut self, source: GospelSourceStructDefinition) -> anyhow::Result<()> {
        for visitor in &mut self.visitors {
            visitor.borrow_mut().define_struct(source.clone())?
        }
        Ok({})
    }
}

/// Implemented by all module visitors that build the containers
pub trait GospelContainerBuilder {
    fn build(&mut self) -> GospelContainer;
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
    lazy_value_lookup: HashMap<GospelLazyValue, u32>,
    struct_lookup: HashMap<String, u32>,
    import_container_struct_lookup: Vec<HashMap<String, u32>>,
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
    fn find_or_add_lazy_value(&mut self, function_index: GospelObjectIndex, arguments: Vec<GospelStaticValue>) -> u32 {
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
    fn find_locally_defined_function_index(&self, function_name: &str) -> anyhow::Result<GospelObjectIndex> {
        self.function_lookup.get(function_name).map(|function_index| {
            GospelObjectIndex::create_local(*function_index)
        }).ok_or_else(|| anyhow!("Failed to find locally defined function {}", function_name.to_string()))
    }
    fn convert_function_reference(&mut self, source: &GospelSourceObjectReference) -> anyhow::Result<GospelObjectIndex> {
        if source.module_name == self.container_name {
            self.find_locally_defined_function_index(source.local_name.as_str())
        } else {
            Ok(GospelObjectIndex::create_external(self.find_or_define_external_function(source.module_name.as_str(), source.local_name.as_str())))
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
                    value_type: GospelValueType::Closure,
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
    fn find_locally_defined_struct_index(&self, struct_name: &str) -> anyhow::Result<GospelObjectIndex> {
        self.struct_lookup.get(struct_name).map(|struct_index| {
            GospelObjectIndex::create_local(*struct_index)
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
            Ok(GospelObjectIndex::create_external(self.find_or_define_external_struct(source.module_name.as_str(), source.local_name.as_str())))
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
        bail!("Function declarations are only allowed when writing reference containers");
    }
    fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        if source.declaration.function_name.module_name != self.container_name {
            return Ok({})
        }
        if self.function_lookup.contains_key(source.declaration.function_name.local_name.as_str()) {
            bail!("Function with name {} is already defined in this container", source.declaration.function_name.local_name);
        }
        if source.declaration.return_value_type.is_none() {
            bail!("Function does not have a valid return value type; all functions must return a value");
        }
        let mut arguments: Vec<GospelFunctionArgument> = Vec::with_capacity(source.declaration.arguments.len());
        for argument in &source.declaration.arguments {
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
        let referenced_structs = source.referenced_structs.iter()
            .map(|x| self.convert_struct_reference(x))
            .collect::<anyhow::Result<Vec<GospelObjectIndex>>>()?;

        let function_index = self.container.functions.len() as u32;
        let function_name_string = source.declaration.function_name.local_name.clone();
        if !source.declaration.hidden {
            let function_name = self.store_string(source.declaration.function_name.local_name.as_str());
            self.container.function_names.push(GospelObjectIndexNamePair { object_index: function_index, object_name: function_name });
        }
        self.container.functions.push(GospelFunctionDefinition {
            arguments, slots,
            return_value_type: source.declaration.return_value_type.unwrap(),
            code: source.code,
            referenced_strings,
            referenced_structs,
        });
        self.function_lookup.insert(function_name_string, function_index);
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
        if !source.hidden {
            let struct_name = self.store_string(source.name.local_name.as_str());
            let field_names: Vec<GospelObjectIndexNamePair> = source.fields.iter()
                .enumerate()
                .filter(|(_, data)| data.field_name.is_some())
                .map(|(index, data)| (index, self.store_string(data.field_name.as_ref().unwrap())))
                .map(|(index, name_index)| GospelObjectIndexNamePair{ object_index: index as u32, object_name: name_index })
                .collect();
            self.container.struct_names.push(GospelStructNameInfo{
                struct_index,
                struct_name,
                field_names,
            })
        }
        self.container.structs.push(GospelStructDefinition {
            fields: source.fields.iter().map(|x| x.field_type).collect(),
        });
        self.struct_lookup.insert(source.name.local_name.clone(), struct_index);
        Ok({})
    }
}
impl GospelContainerBuilder for GospelContainerWriter {
    fn build(&mut self) -> GospelContainer {
        std::mem::take(&mut self.container)
    }
}

/// Implementation of the visitor that writes reference containers. Reference containers do not contain implementations or private types
#[derive(Debug, Clone)]
pub struct GospelReferenceContainerWriter {
    container_writer: GospelContainerWriter,
}
impl GospelReferenceContainerWriter {
    /// Creates a new reference container writer
    pub fn create(container_name: &str) -> Self {
        let mut writer = GospelContainerWriter::create(container_name);
        writer.container.header.is_reference_container = true;
        Self{container_writer: writer}
    }
}
impl GospelModuleVisitor for GospelReferenceContainerWriter {
    fn module_name(&self) -> Option<String> {
        self.container_writer.module_name()
    }
    fn declare_global(&mut self, name: &str) -> anyhow::Result<()> {
        self.container_writer.declare_global(name)
    }
    fn define_global(&mut self, name: &str, _value: i32) -> anyhow::Result<()> {
        self.container_writer.declare_global(name)
    }
    fn declare_function(&mut self, mut source: GospelSourceFunctionDeclaration) -> anyhow::Result<()> {
        if source.return_value_type.is_none() {
            bail!("Function does not have a valid return value type; all functions must return a value");
        }
        source.arguments.iter_mut().for_each(|argument| {
            if argument.default_value.is_some() {
                argument.default_value = Some(GospelSourceStaticValue::Integer(0))
            }
        });
        if !source.hidden {
            let mut function_definition = GospelSourceFunctionDefinition::create(source);
            function_definition.add_string_instruction(GospelOpcode::Abort, "Attempting to execute a function stub")?;
            self.container_writer.define_function(function_definition)
        } else { Ok({}) }
    }
    fn define_function(&mut self, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        self.declare_function(source.declaration)
    }
    fn define_struct(&mut self, source: GospelSourceStructDefinition) -> anyhow::Result<()> {
        if !source.hidden {
            self.container_writer.define_struct(source)
        } else { Ok({}) }
    }
}
impl GospelContainerBuilder for GospelReferenceContainerWriter {
    fn build(&mut self) -> GospelContainer {
        self.container_writer.build()
    }
}
