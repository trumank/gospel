use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::str::FromStr;
use anyhow::{anyhow, bail};
use serde::{Deserialize, Serialize};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::module::{GospelContainer, GospelContainerImport, GospelContainerVersion, GospelGlobalDefinition};
use crate::gospel::{GospelExternalObjectReference, GospelFunctionDefinition, GospelObjectIndex, GospelFunctionDebugData};

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
impl FromStr for GospelSourceObjectReference {
    type Err = anyhow::Error;
    fn from_str(s: &str) -> anyhow::Result<Self> {
        let module_split_index = s.find(':').ok_or_else(|| anyhow!("Expected module:name format"))?;
        let module_name = s[0..module_split_index].to_string();
        let local_name = s[module_split_index + 1..].to_string();
        Ok(Self{module_name, local_name})
    }
}

/// Represents a fixup that needs to be applied to the control flow instruction
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GospelJumpLabelFixup {
    pub instruction_index: u32,
    pub operand_index: u32,
}

/// Allows building definitions of functions to be added to the container writer later
#[derive(Debug, Clone, Default)]
pub struct GospelSourceFunctionDefinition {
    pub exported: bool,
    pub num_slots: u32,
    code: Vec<GospelInstruction>,
    referenced_strings: Vec<String>,
    referenced_functions: Vec<GospelSourceObjectReference>,
    referenced_string_lookup: HashMap<String, u32>,
    referenced_functions_lookup: HashMap<GospelSourceObjectReference, u32>,
    pub source_file_name: String,
    debug_instruction_line_numbers: Vec<i32>,
}
impl GospelSourceFunctionDefinition {
    /// Creates a named function from a declaration
    pub fn create(exported: bool, source_file_name: String) -> Self {
        Self{exported, source_file_name, ..GospelSourceFunctionDefinition::default()}
    }
    pub fn add_slot(&mut self) -> anyhow::Result<u32> {
        let new_slot_index = self.num_slots;
        self.num_slots += 1;
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
    pub fn add_function_reference_internal(&mut self, function_reference: GospelSourceObjectReference) -> u32 {
        if let Some(existing_index) = self.referenced_functions_lookup.get(&function_reference) {
            return *existing_index
        }
        let new_function_index = self.referenced_functions.len() as u32;
        self.referenced_functions.push(function_reference.clone());
        self.referenced_functions_lookup.insert(function_reference, new_function_index);
        new_function_index
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
        if slot_index as usize >= self.num_slots as usize {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", slot_index, self.num_slots);
        }
        if opcode != GospelOpcode::LoadSlot && opcode != GospelOpcode::StoreSlot && opcode != GospelOpcode::TakeSlot {
            bail!("Invalid opcode for slot instruction (LoadSlot, StoreSlot and TakeSlot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[slot_index])?, line_number))
    }
    pub fn add_load_argument_value_instruction(&mut self, argument_index: u32, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::LoadArgumentValue, &[argument_index])?, line_number))
    }
    pub fn add_int_instruction(&mut self, opcode: GospelOpcode, value: u32, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[value])?, line_number))
    }
    pub fn add_int64_constant_instruction(&mut self, value: u64, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::Int64Constant, &[(value >> 32) as u32, value as u32])?, line_number))
    }
    pub fn add_control_flow_instruction_no_fixup(&mut self, opcode: GospelOpcode, target_instruction_index: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::PushExceptionHandler {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[target_instruction_index])?, line_number))
    }
    pub fn add_control_flow_instruction(&mut self, opcode: GospelOpcode, line_number: i32) -> anyhow::Result<(u32, GospelJumpLabelFixup)> {
        if opcode != GospelOpcode::Branch && opcode != GospelOpcode::PushExceptionHandler {
            bail!("Invalid opcode for control flow instruction (Branch and BranchIfNot are allowed)");
        }
        let jump_instruction = self.add_instruction_internal(GospelInstruction::create(opcode, &[u32::MAX])?, line_number);
        Ok((jump_instruction, GospelJumpLabelFixup{instruction_index: jump_instruction, operand_index: 0}))
    }
    pub fn add_conditional_branch_instruction(&mut self, instruction_encoding: u32, line_number: i32) -> anyhow::Result<(u32, GospelJumpLabelFixup)> {
        let jump_instruction = self.add_instruction_internal(GospelInstruction::create(GospelOpcode::Branchz, &[instruction_encoding, u32::MAX])?, line_number);
        Ok((jump_instruction, GospelJumpLabelFixup{instruction_index: jump_instruction, operand_index: 1}))
    }
    pub fn fixup_control_flow_instruction(&mut self, fixup: GospelJumpLabelFixup, target_instruction_index: u32) -> anyhow::Result<()> {
        if fixup.instruction_index as usize >= self.code.len() {
            bail!("Invalid fixup instruction index #{} out of bounds", fixup.instruction_index);
        }
        self.code[fixup.instruction_index as usize].set_immediate_operand(fixup.operand_index as usize, target_instruction_index)
    }
    pub fn add_string_instruction(&mut self, opcode: GospelOpcode, string: &str, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeUDTHasField && opcode != GospelOpcode::TypeUDTTypeofField &&
            opcode != GospelOpcode::TypeUDTCalculateVirtualFunctionOffset && opcode != GospelOpcode::RaiseException &&
            opcode != GospelOpcode::TypePrimitiveCreate && opcode != GospelOpcode::LoadTargetProperty &&
            opcode != GospelOpcode::LoadGlobalVariable && opcode != GospelOpcode::StructAllocate &&
            opcode != GospelOpcode::StructGetField && opcode != GospelOpcode::StructSetField {
            bail!("Invalid opcode for named instruction");
        }
        let string_index = self.add_string_reference_internal(string);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[string_index])?, line_number))
    }
    pub fn add_type_allocate_instruction(&mut self, opcode: GospelOpcode, name: &str, udt_kind: &str, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeUDTAllocate &&opcode != GospelOpcode::TypeEnumAllocate {
            bail!("Invalid opcode for type allocate instruction (TypeUDTAllocate, TypeEnumAllocate are allowed)");
        }
        let name_index = self.add_string_reference_internal(name);
        let udt_kind_index = self.add_string_reference_internal(udt_kind);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[name_index, udt_kind_index])?, line_number))
    }
    pub fn add_udt_base_class_instruction(&mut self, base_class_flags: u32, line_number: i32) -> anyhow::Result<u32> {
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::TypeUDTAddBaseClass, &[base_class_flags])?, line_number))
    }
    pub fn add_type_member_instruction(&mut self, opcode: GospelOpcode, name: Option<&String>, flags: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::TypeUDTAddField && opcode != GospelOpcode::TypeUDTAddBitfield && opcode != GospelOpcode::TypeEnumAddConstant {
            bail!("Invalid opcode for udt member instruction (TypeUDTAddField, TypeUDTAddBitfield, TypeEnumAddConstant are allowed)");
        }
        let name_index = if let Some(name_str) = name { self.add_string_reference_internal(name_str) } else { -1i32 as u32 };
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[name_index, flags])?, line_number))
    }
    pub fn add_enum_constant_with_value_instruction(&mut self, name: Option<&String>, flags: u32, instruction_encoding: u32, line_number: i32) -> anyhow::Result<u32> {
        let name_index = if let Some(name_str) = name { self.add_string_reference_internal(name_str) } else { -1i32 as u32 };
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::TypeEnumAddConstantWithValue, &[name_index, flags, instruction_encoding])?, line_number))
    }
    pub fn add_udt_virtual_function_instruction(&mut self, name: &str, function_flags: u32, argument_count: u32, line_number: i32) -> anyhow::Result<u32> {
        let name_index = self.add_string_reference_internal(name);
        Ok(self.add_instruction_internal(GospelInstruction::create(GospelOpcode::TypeUDTAddVirtualFunction, &[name_index, function_flags, argument_count])?, line_number))
    }
    pub fn add_function_instruction(&mut self, opcode: GospelOpcode, function_reference: GospelSourceObjectReference, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::LoadFunctionClosure {
            bail!("Invalid opcode for typed member access instruction (only LoadFunctionClosure is allowed)");
        }
        let function_index = self.add_function_reference_internal(function_reference);
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[function_index])?, line_number))
    }
    pub fn add_variadic_instruction(&mut self, opcode: GospelOpcode, argument_count: u32, line_number: i32) -> anyhow::Result<u32> {
        if opcode != GospelOpcode::Call && opcode != GospelOpcode::BindClosure && opcode != GospelOpcode::TypeFunctionCreateMember && opcode != GospelOpcode::TypeFunctionCreateGlobal {
            bail!("Invalid opcode for variadic instruction (only Call, BindClosure, PCall and TypeFunctionCreateMember/Global are allowed)");
        }
        Ok(self.add_instruction_internal(GospelInstruction::create(opcode, &[argument_count])?, line_number))
    }
}

/// Generic sink for building gospel modules (into containers or reference containers)
pub trait GospelModuleVisitor : Debug {
    fn module_name(&self) -> Option<String>;
    fn define_global(&mut self, name: &str, default_value: u64) -> anyhow::Result<()>;
    fn declare_function(&mut self, name: GospelSourceObjectReference) -> anyhow::Result<()>;
    fn define_function(&mut self, name: GospelSourceObjectReference, source: GospelSourceFunctionDefinition) -> anyhow::Result<()>;
}

/// Implemented by all module visitors that build the containers
pub trait GospelContainerBuilder : Debug {
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
    pending_function_declarations: HashSet<u32>,
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
}
impl GospelModuleVisitor for GospelContainerWriter {
    fn module_name(&self) -> Option<String> {
        Some(self.container_name.clone())
    }
    fn define_global(&mut self, name: &str, value: u64) -> anyhow::Result<()> {
        if let Some(existing_global_index) = self.globals_lookup.get(name) {
            let existing_global = &mut self.container.globals[*existing_global_index as usize];
            if existing_global.default_value != value {
                bail!("Multiple global definition for global {} using different default value (previously set to {}, now defined as {})",
                    name.to_string(), existing_global.default_value, value);
            }
            Ok({})
        } else {
            let new_global_index = self.container.globals.len() as u32;
            let name_index = self.store_string(name);
            self.container.globals.push(GospelGlobalDefinition{ name: name_index, default_value: value });
            self.globals_lookup.insert(name.to_string(), new_global_index);
            Ok({})
        }
    }
    fn declare_function(&mut self, function_name: GospelSourceObjectReference) -> anyhow::Result<()> {
        if function_name.module_name != self.container_name {
            return Ok({})
        }
        if self.function_lookup.get(&function_name.local_name).is_none() {
            // This function has not been declared or defined yet, so declare it now
            let function_name_index = self.store_string(function_name.local_name.as_str());

            let placeholder_function_definition = GospelFunctionDefinition{
                name: function_name_index,
                num_slots: 0,
                exported: false,
                code: Vec::new(),
                referenced_strings: Vec::new(),
                referenced_functions: Vec::new(),
                debug_data: None,
            };
            let function_index = self.container.functions.len() as u32;
            self.container.functions.push(placeholder_function_definition);
            self.pending_function_declarations.insert(function_index);

            let function_name_string = function_name.local_name.clone();
            self.function_lookup.insert(function_name_string, function_index);
        }
        Ok({})
    }
    fn define_function(&mut self, function_name: GospelSourceObjectReference, source: GospelSourceFunctionDefinition) -> anyhow::Result<()> {
        if function_name.module_name != self.container_name {
            return Ok({})
        }

        let referenced_strings: Vec<u32> = source.referenced_strings.iter().map(|x| {
            self.store_string(x.as_str())
        }).collect();
        let referenced_functions = source.referenced_functions.iter()
            .map(|x| self.convert_function_reference(x))
            .collect::<anyhow::Result<Vec<GospelObjectIndex>>>()?;

        let function_name_index = self.store_string(function_name.local_name.as_str());
        let debug_data = GospelFunctionDebugData{
            source_file_name: self.store_string(source.source_file_name.as_str()),
            instruction_line_numbers: source.debug_instruction_line_numbers,
        };

        let result_function_definition = GospelFunctionDefinition {
            name: function_name_index,
            exported: source.exported,
            num_slots: source.num_slots,
            code: source.code,
            referenced_strings,
            referenced_functions,
            debug_data: Some(debug_data),
        };

        if let Some(existing_function_index) = self.function_lookup.get(&function_name.local_name) {
            if self.pending_function_declarations.contains(existing_function_index) {
                // Update the function definition now
                self.container.functions[*existing_function_index as usize] = result_function_definition;
                self.pending_function_declarations.remove(existing_function_index);
            } else {
                // No pending pre-declaration, this is a conflicting definition of a previously defined function
                bail!("Function with name {} is already defined in this container", function_name.local_name);
            }
        } else {
            // No existing function with the same, define the function now
            let function_index = self.container.functions.len() as u32;
            self.container.functions.push(result_function_definition);

            let function_name_string = function_name.local_name.clone();
            self.function_lookup.insert(function_name_string, function_index);
        }
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
