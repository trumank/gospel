use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::rc::Rc;
use anyhow::{anyhow, bail};
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::GospelContainer;
use crate::gospel_type::{GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelStaticValueType, GospelTargetArch, GospelTargetEnv, GospelTargetOS, GospelTypeDefinition, GospelTypeIndex, GospelValueType};

#[derive(Debug, Clone)]
pub struct GospelBaseClassLayout {
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

#[derive(Debug, Clone)]
pub struct GospelMemberLayout {
    pub name: String,
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

/// Represents a fully resolved layout of a particular type
/// This exposes information such as the size of the type, its alignment, unaligned size,
/// and offsets, sizes and full type layouts of its members
#[derive(Debug, Clone, Default)]
pub struct GospelTypeLayout {
    pub name: String,
    pub alignment: usize,
    pub unaligned_size: usize,
    pub size: usize,
    pub base_classes: Vec<GospelBaseClassLayout>,
    pub members: Vec<GospelMemberLayout>,
    pub source_type: Option<GospelVMTypeReference>,
    pub source_args: Option<Vec<GospelVMValue>>,
}
impl GospelTypeLayout {
    // Note that types with no source information are never considered source identical
    pub fn source_identical(&self, other: &Self) -> bool {
        self.source_type.is_some() && other.source_type.is_some() &&
            self.source_type.as_ref().unwrap().reference_identical(other.source_type.as_ref().unwrap()) &&
            self.source_args == other.source_args
    }
    // Note that returned base offset is absolute, not relative to the parent offset
    pub fn get_base_offset(&self, base: &Self) -> Option<usize> {
        if self.source_identical(base) {
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
    pub fn address_size(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    fn uses_aligned_base_class_size(&self) -> bool {
        self.env == GospelTargetEnv::MSVC // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
}

/// Represents reference to a particular type located inside a particular container
/// Type cannot be used directly; type instances can be created and their layouts investigated
/// by using GospelVMTypeReference:resolve with the required template arguments
/// Two type references are identical if they point to the type with the same name in the same container
#[derive(Debug, Clone)]
pub struct GospelVMTypeReference {
    container: Rc<GospelVMContainer>,
    type_index: u32,
}
impl GospelVMTypeReference {
    pub fn reference_identical(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.container, &other.container) && self.type_index == other.type_index
    }
}
impl GospelVMTypeReference {
    /// Returns the type container which defines this type
    pub fn source_container(&self) -> Rc<GospelVMContainer> {
        self.container.clone()
    }
    /// Returns the name of the type referenced
    pub fn type_name(&self) -> anyhow::Result<&str> {
        self.container.get_type_name(self.type_index)
    }
    /// Attempts to resolve the layout of this type using the arguments provided
    pub fn resolve_layout(&self, args: &Vec<GospelVMValue>) -> anyhow::Result<GospelTypeLayout> {
        self.container.resolve_layout_internal(self.type_index, args)
    }
    fn resolve_layout_static(&self, args: &Vec<GospelStaticValue>) -> anyhow::Result<GospelTypeLayout> {
        self.container.resolve_layout_static(self.type_index, args)
    }
}

/// VM Value represents a value that VM bytecode can read and write
/// Currently supported value types are integers, type references and type layouts
/// Type references can be converted into type layouts by providing them with arguments
/// Values can be compared for equality, but values of certain types might never be equivalent (for example, unnamed type layouts are never equivalent, even to themselves)
#[derive(Debug, Clone)]
pub enum GospelVMValue {
    Integer(i32), // signed 32-bit integer value
    TypeDefinition(GospelVMTypeReference), // definition of a type with no template arguments
    TypeLayout(GospelTypeLayout), // pre-computed type layout
}
impl GospelVMValue {
    pub fn value_type(&self) -> GospelValueType {
        match self {
            GospelVMValue::Integer(_) => { GospelValueType::Integer }
            GospelVMValue::TypeDefinition(_) => { GospelValueType::TypeReference }
            GospelVMValue::TypeLayout(_) => { GospelValueType::TypeLayout }
        }
    }
}
impl PartialEq for GospelVMValue {
    fn eq(&self, other: &Self) -> bool {
        match self {
            GospelVMValue::Integer(a) => match other {
                GospelVMValue::Integer(b) => { *a == *b }
                _ => false
            }
            GospelVMValue::TypeDefinition(a) => match other {
                GospelVMValue::TypeDefinition(b) => { a.reference_identical(b) }
                _ => false
            }
            GospelVMValue::TypeLayout(a) => match other {
                GospelVMValue::TypeLayout(b) => { a.source_identical(b) }
                _ => false
            }
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
    pub target_triplet: &'a GospelVMTargetTriplet,
    pub instructions: &'a Vec<GospelInstruction>,
    pub slot_definitions: &'a Vec<GospelSlotDefinition>,
    pub layout_builder: GospelTypeLayout,
    pub slots: Vec<Option<GospelVMValue>>,
    pub referenced_strings: Vec<String>,
    pub stack: Vec<GospelVMValue>,
    pub current_instruction_index: usize,
    pub current_loop_jump_count: usize,
    pub max_stack_size: usize,
    pub max_loop_jumps: usize,
}
impl GospelVMExecutionState<'_> {
    fn align_value(value: usize, align: usize) -> usize {
        let reminder = value % align;
        if reminder == 0 { value } else { value + (align - reminder) }
    }
    fn push_stack_check_overflow(&mut self, value: GospelVMValue) -> anyhow::Result<()> {
        if self.stack.len() > self.max_stack_size {
            bail!("Stack overflow");
        }
        self.stack.push(value);
        Ok({})
    }
    fn pop_stack_check_underflow(&mut self) -> anyhow::Result<GospelVMValue> {
        if self.stack.len() == 0 {
            bail!("Stack underflow");
        }
        Ok(self.stack.pop().unwrap())
    }
    fn jump_control_flow_checked(&mut self, target_index: usize) -> anyhow::Result<()> {
        if target_index >= self.instructions.len() {
            bail!("Invalid control flow jump to instruction index #{} out of bounds (number of instructions: {})", target_index, self.instructions.len());
        }
        // If we are jumping back, this is a loop, and we need to check the loop limit
        if target_index < self.current_instruction_index {
            self.current_loop_jump_count += 1;
            if self.current_loop_jump_count > self.max_loop_jumps {
                bail!("Loop limit reached");
            }
        }
        self.current_instruction_index = target_index;
        Ok({})
    }
    fn read_slot_value_checked(&mut self, index: usize) -> anyhow::Result<GospelVMValue> {
        if index >= self.slots.len() {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", index, self.slots.len());
        }
        self.slots[index].clone().ok_or_else(|| anyhow!("Invalid read of uninitialized data from slot at index #{}", index))
    }
    fn write_slot_value_checked(&mut self, index: usize, value: GospelVMValue) -> anyhow::Result<()> {
        if index >= self.slots.len() {
            bail!("Invalid slot index #{} out of bounds (number of slots: {})", index, self.slots.len());
        }
        if self.slot_definitions[index].value_type != value.value_type() {
            bail!("Invalid write of incompatible value type to slot at index #{}", index);
        }
        self.slots[index] = Some(value);
        Ok({})
    }
    fn immediate_value_checked(inst: &GospelInstruction, index: usize) -> anyhow::Result<u32> {
        inst.immediate_operand_at(index).ok_or_else(|| anyhow!("Invalid instruction encoding: Missing immediate operand #{}", index))
    }
    fn copy_referenced_string_checked(&self, index: usize) -> anyhow::Result<String> {
        if index >= self.referenced_strings.len() {
            bail!("Invalid referenced string index #{} out of bounds (number of referenced strings: {})", index, self.referenced_strings.len());
        }
        Ok(self.referenced_strings[index].clone())
    }
    fn unwrap_value_as_int_checked(value: GospelVMValue) -> anyhow::Result<i32> {
        match value {
            GospelVMValue::Integer(unwrapped) => { Ok(unwrapped) }
            _ => bail!("Expected integer value, got value of different type")
        }
    }
    fn unwrap_value_as_type_definition_checked(value: GospelVMValue) -> anyhow::Result<GospelVMTypeReference> {
        match value {
            GospelVMValue::TypeDefinition(unwrapped) => { Ok(unwrapped) }
            _ => bail!("Expected type definition value, got value of different type")
        }
    }
    fn unwrap_value_as_type_layout_checked(value: GospelVMValue) -> anyhow::Result<GospelTypeLayout> {
        match value {
            GospelVMValue::TypeLayout(unwrapped) => { Ok(unwrapped) }
            _ => bail!("Expected type layout value, got value of different type")
        }
    }
    fn do_bitwise_op<F: Fn(u32, u32) -> u32>(&mut self, op: F) -> anyhow::Result<()> {
        let stack_value_a = Self::unwrap_value_as_int_checked(self.pop_stack_check_underflow()?)? as u32;
        let stack_value_b = Self::unwrap_value_as_int_checked(self.pop_stack_check_underflow()?)? as u32;
        let result = op(stack_value_a, stack_value_b) as i32;
        self.push_stack_check_overflow(GospelVMValue::Integer(result))
    }
    fn do_arithmetic_op_checked<F: Fn(i32, i32) -> anyhow::Result<i32>>(&mut self, op: F) -> anyhow::Result<()> {
        let stack_value_a = Self::unwrap_value_as_int_checked(self.pop_stack_check_underflow()?)?;
        let stack_value_b = Self::unwrap_value_as_int_checked(self.pop_stack_check_underflow()?)?;
        let result = op(stack_value_a, stack_value_b)?;
        self.push_stack_check_overflow(GospelVMValue::Integer(result))
    }
    fn do_member_access_op_checked<F: Fn(GospelMemberLayout) -> GospelVMValue>(&mut self, member_name_index: usize, op: F) -> anyhow::Result<()> {
        let member_name = self.copy_referenced_string_checked(member_name_index)?;
        let type_layout = Self::unwrap_value_as_type_layout_checked(self.pop_stack_check_underflow()?)?;

        let result_member = type_layout.find_named_member(member_name.as_str()).ok_or_else(|| {
            anyhow!("Failed to find member named {} inside type {}", member_name.clone(), type_layout.name.clone())
        })?;
        op(result_member);
        Ok({})
    }
    fn run(state: &mut GospelVMExecutionState) -> anyhow::Result<GospelTypeLayout> {
        // Set up defaults for alignment and unaligned size
        state.layout_builder.alignment = 1;
        state.layout_builder.unaligned_size = 0;
        state.layout_builder.size = 0;

        // Main VM loop
        state.current_instruction_index = 0;
        state.current_loop_jump_count = 0;
        while state.current_instruction_index < state.instructions.len() {
            let instruction = &state.instructions[state.current_instruction_index];
            let opcode = instruction.opcode().ok_or_else(|| {
                anyhow!("Unknown opcode {:x}", instruction.raw_opcode())
            })?;
            state.current_instruction_index += 1;

            match opcode {
                // Basic opcodes
                GospelOpcode::Noop => {}
                GospelOpcode::IntConstant => {
                    let int_value = Self::immediate_value_checked(instruction, 0)? as i32;
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
                    let result = stack_value_a == stack_value_b;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::Return => {
                    break;
                }
                // Structure opcodes
                GospelOpcode::Align => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let alignment = Self::unwrap_value_as_int_checked(stack_value)? as usize;
                    state.layout_builder.alignment = max(state.layout_builder.alignment, alignment);
                    state.layout_builder.unaligned_size = Self::align_value(state.layout_builder.unaligned_size, alignment);
                }
                GospelOpcode::Pad => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let padding_bytes = Self::unwrap_value_as_int_checked(stack_value)? as usize;
                    state.layout_builder.unaligned_size += padding_bytes;
                }
                GospelOpcode::BaseClass => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let base_class_layout = Self::unwrap_value_as_type_layout_checked(stack_value)?;

                    // Make sure the alignment requirement is met for the base class
                    state.layout_builder.alignment = max(state.layout_builder.alignment, base_class_layout.alignment);
                    state.layout_builder.unaligned_size = Self::align_value(state.layout_builder.unaligned_size, base_class_layout.alignment);

                    // Actual class size differs depending on ABI used, on MSVC aligned base class size is used, while on GNU/Darwin
                    // unaligned class size is used, saving some space on derived types that are inherited from base classes ending with alignment padding
                    let actual_base_class_size = if state.target_triplet.uses_aligned_base_class_size() {
                        base_class_layout.size
                    } else { base_class_layout.unaligned_size };

                    state.layout_builder.base_classes.push(GospelBaseClassLayout{
                        offset: state.layout_builder.unaligned_size,
                        actual_size: actual_base_class_size,
                        layout: base_class_layout,
                    });
                    state.layout_builder.unaligned_size += actual_base_class_size;
                }
                GospelOpcode::Member => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let stack_value = state.pop_stack_check_underflow()?;
                    let member_layout = Self::unwrap_value_as_type_layout_checked(stack_value)?;

                    // Make sure the alignment requirement is met for the member
                    state.layout_builder.alignment = max(state.layout_builder.alignment, member_layout.alignment);
                    state.layout_builder.unaligned_size = Self::align_value(state.layout_builder.unaligned_size, member_layout.alignment);

                    let actual_size = member_layout.size;
                    state.layout_builder.members.push(GospelMemberLayout{
                        name: member_name,
                        offset: state.layout_builder.unaligned_size,
                        actual_size,
                        layout: member_layout,
                    });
                    state.layout_builder.unaligned_size += actual_size;
                }
                GospelOpcode::ReturnTypeLayout => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let redirected_layout = Self::unwrap_value_as_type_layout_checked(stack_value)?;
                    // This type is a type alias, as such its layout is actually a layout of another type (likely dynamically constructed earlier)
                    return Ok(redirected_layout)
                }
                // Logical opcodes
                GospelOpcode::And => { state.do_bitwise_op(|a, b| a & b)?; }
                GospelOpcode::Or => { state.do_bitwise_op(|a, b| a | b)?; }
                GospelOpcode::Xor => { state.do_bitwise_op(|a, b| a ^ b)?; }
                GospelOpcode::Shl => { state.do_bitwise_op(|a, b| a >> b)?; }
                GospelOpcode::Shr => { state.do_bitwise_op(|a, b| a << b)?; }
                GospelOpcode::ReverseBits => {
                    let stack_value = Self::unwrap_value_as_int_checked(state.pop_stack_check_underflow()?)? as u32;
                    let result = stack_value.reverse_bits() as i32;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                // Arithmetic opcodes
                GospelOpcode::Add => { state.do_arithmetic_op_checked(|a, b| Ok(a + b))?; }
                GospelOpcode::Sub => { state.do_arithmetic_op_checked(|a, b| Ok(a - b))?; }
                GospelOpcode::Mul => { state.do_arithmetic_op_checked(|a, b| Ok(a * b))?; }
                GospelOpcode::Div => {
                    state.do_arithmetic_op_checked(|a, b| {
                        if b == 0 { Err(anyhow!("Division by zero")) } else { Ok(a / b) }
                    })?;
                }
                GospelOpcode::Rem => {
                    state.do_arithmetic_op_checked(|a, b| {
                        if b == 0 { Err(anyhow!("Division by zero")) } else { Ok(a % b) }
                    })?;
                }
                GospelOpcode::Neg => {
                    let stack_value = Self::unwrap_value_as_int_checked(state.pop_stack_check_underflow()?)?;
                    let result = -stack_value;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result))?;
                }
                // Control flow opcodes
                GospelOpcode::Branch => {
                    let target_instruction_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    state.jump_control_flow_checked(target_instruction_index)?;
                }
                GospelOpcode::BranchIfNot => {
                    let target_instruction_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let condition_value = Self::unwrap_value_as_int_checked(state.pop_stack_check_underflow()?)? as u32;
                    if condition_value == 0 {
                        state.jump_control_flow_checked(target_instruction_index)?;
                    }
                }
                // Data storage opcodes
                GospelOpcode::LoadSlot => {
                    let slot_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let current_slot_value = state.read_slot_value_checked(slot_index)?;
                    state.push_stack_check_overflow(current_slot_value)?;
                }
                GospelOpcode::StoreSlot => {
                    let slot_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let new_slot_value = state.pop_stack_check_underflow()?;
                    state.write_slot_value_checked(slot_index, new_slot_value)?;
                }
                // Type opcodes
                GospelOpcode::CreateTypeLayout => {
                    let number_of_arguments = Self::immediate_value_checked(instruction, 0)? as usize;
                    let type_definition = Self::unwrap_value_as_type_definition_checked(state.pop_stack_check_underflow()?)?;
                    let mut type_arguments: Vec<GospelVMValue> = Vec::with_capacity(number_of_arguments);
                    for _ in 0..number_of_arguments {
                        type_arguments.push(state.pop_stack_check_underflow()?);
                    }
                    let resolved_layout = type_definition.resolve_layout(&type_arguments).map_err(|err| {
                        let type_name = type_definition.type_name().unwrap_or("<unknown>");
                        anyhow!("Failed to resolve type layout for type definition {}: {}", type_name.to_string(), err.to_string())
                    })?;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(resolved_layout))?;
                }
                GospelOpcode::TypeLayoutGetSize => {
                    let type_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.size as i32))?;
                }
                GospelOpcode::TypeLayoutGetAlignment => {
                    let type_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.alignment as i32))?;
                }
                GospelOpcode::TypeLayoutGetUnalignedSize => {
                    let type_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.unaligned_size as i32))?;
                }
                GospelOpcode::TypeLayoutDoesMemberExist => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;
                    let type_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    let result = type_layout.members.iter().any(|x| x.name == member_name);
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberSize => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::Integer(x.actual_size as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberOffset => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::Integer(x.offset as i32))?;
                }
                GospelOpcode::TypeLayoutGetMemberTypeLayout => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    state.do_member_access_op_checked(member_name_index, |x| GospelVMValue::TypeLayout(x.layout))?;
                }
                GospelOpcode::TypeLayoutIsChildOf => {
                    let child_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    let parent_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    let result = child_layout.get_base_offset(&parent_layout).is_some();
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::TypeLayoutGetOffsetOfBase => {
                    let child_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    let parent_layout = Self::unwrap_value_as_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    let result = child_layout.get_base_offset(&parent_layout)
                        .ok_or_else(|| anyhow!("Type {} is not a base of type {}", child_layout.name.clone(), parent_layout.name.clone()))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
            };
        }

        // Make sure the size is at least one byte, and calculate the aligned size from unaligned size
        if state.layout_builder.unaligned_size == 0 {
           state.layout_builder.unaligned_size = 1;
        }
        state.layout_builder.size = Self::align_value(state.layout_builder.unaligned_size, state.layout_builder.alignment);
        Ok(state.layout_builder.clone())
    }
}

#[derive(Debug)]
pub struct GospelVMContainer {
    target_triplet: GospelVMTargetTriplet,
    container: Rc<GospelContainer>,
    external_references: Vec<Rc<GospelVMContainer>>,
    global_lookup_by_id: HashMap<usize, Rc<GospelGlobalStorage>>,
    type_lookup_by_name: HashMap<String, u32>,
}
impl GospelVMContainer {
    /// Returns the name of this type container
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.container.container_name()
    }
    /// Attempts to find a type with the given name in this container and returns a reference to it
    pub fn find_named_type(self: &Rc<Self>, name: &str) -> Option<GospelVMTypeReference> {
        self.type_lookup_by_name.get(name).map(|type_index| GospelVMTypeReference{
            container: self.clone(), type_index: *type_index })
    }
    fn get_type_name(&self, index: u32) -> anyhow::Result<&str> {
        let type_definition = &self.container.types[index as usize];
        self.container.strings.get(type_definition.type_name)
    }
    fn resolve_type_index(self: &Rc<Self>, type_index: GospelTypeIndex) -> anyhow::Result<GospelVMTypeReference> {
        if type_index.is_external() {
            if type_index.index() as usize >= self.container.external_types.len() {
                bail!("Invalid external type index #{} out of bounds (num external type references in container: {})", type_index.index(), self.container.external_types.len());
            }
            let external_type = &self.container.external_types[type_index.index() as usize];
            if external_type.import_index as usize >= self.external_references.len() {
                bail!("Invalid external container reference index #{} out of bounds (num external container references: {})", external_type.import_index, self.external_references.len());
            }
            let source_container = &self.external_references[external_type.import_index as usize];
            let type_name = self.container.strings.get(external_type.type_name)?;
            return source_container.find_named_type(type_name)
                .ok_or_else(|| { anyhow!("Imported named type {} does not exist in container {}", self.container_name().unwrap(), type_name.to_string()) });
        }
        Ok(GospelVMTypeReference{ container: self.clone(), type_index: type_index.index() })
    }
    fn resolve_static_type_instance_layout(self: &Rc<Self>, index: u32) -> anyhow::Result<GospelTypeLayout> {
        if index as usize >= self.container.static_instances.len() {
            bail!("Invalid static type instance index #{} out of bounds (num static type instances in container: {})", index, self.container.static_instances.len());
        }
        let type_instance = &self.container.static_instances[index as usize];
        let type_reference = self.resolve_type_index(type_instance.type_index)?;
        type_reference.resolve_layout_static(&type_instance.arguments)
    }
    fn resolve_static_value(self: &Rc<Self>, value: &GospelStaticValue) -> anyhow::Result<GospelVMValue> {
        match value.value_type {
            GospelValueType::Integer => {
                match value.static_type {
                    GospelStaticValueType::Integer => {
                        Ok(GospelVMValue::Integer(value.data as i32))
                    }
                    _ => bail!("Invalid static initializer for integer value")
                }
            }
            GospelValueType::TypeReference => {
                match value.static_type {
                    GospelStaticValueType::TypeReference => {
                        let type_index = GospelTypeIndex::create_raw(value.data);
                        let reference = self.resolve_type_index(type_index)?;
                        Ok(GospelVMValue::TypeDefinition(reference))
                    }
                    _ => bail!("Invalid static initializer for type definition")
                }
            }
            GospelValueType::TypeLayout => {
                match value.static_type {
                    GospelStaticValueType::StaticTypeInstance => {
                        let layout = self.resolve_static_type_instance_layout(value.data)?;
                        Ok(GospelVMValue::TypeLayout(layout))
                    }
                    _ => bail!("Invalid static initializer for type layout")
                }
            }
        }
    }
    fn resolve_layout_static(self: &Rc<Self>, index: u32, args: &Vec<GospelStaticValue>) -> anyhow::Result<GospelTypeLayout> {
        let mut resolved_args: Vec<GospelVMValue> = Vec::new();
        for argument_index in 0..args.len() {
            let resolved_value = self.resolve_static_value(&args[argument_index])
                .map_err(|x| anyhow!("Failed to resolve template argument #{} value: {}", argument_index, x.to_string()))?;
            resolved_args.push(resolved_value)
        }
        self.resolve_layout_internal(index, &resolved_args)
    }
    fn resolve_platform_config_property(&self, property: GospelPlatformConfigProperty) -> i32 {
        match property {
            GospelPlatformConfigProperty::TargetArch => { self.target_triplet.arch as i32 }
            GospelPlatformConfigProperty::TargetOS => { self.target_triplet.sys as i32 }
            GospelPlatformConfigProperty::TargetEnv => { self.target_triplet.env as i32 }
            GospelPlatformConfigProperty::AddressSize => { self.target_triplet.address_size() as i32 }
        }
    }
    fn resolve_slot_binding(self: &Rc<Self>, type_definition: &GospelTypeDefinition, slot: &GospelSlotDefinition, args: &Vec<GospelVMValue>) -> anyhow::Result<Option<GospelVMValue>> {
        match slot.binding {
            GospelSlotBinding::Uninitialized => {
                Ok(None)
            }
            GospelSlotBinding::StaticValue => {
                if slot.value_type != slot.binding_data.value_type {
                    bail!("Slot value type is not compatible with static value type specified")
                }
                let resolved_value = self.resolve_static_value(&slot.binding_data)?;
                Ok(Some(resolved_value))
            }
            GospelSlotBinding::GlobalVariableValue => {
                if slot.binding_data.value_type != GospelValueType::Integer {
                    bail!("Invalid input variable slot binding data, expected value type to be integer")
                }
                // For now all global variables are integers
                if slot.value_type != GospelValueType::Integer {
                    bail!("Slot value type is not compatible with global variable value type")
                }

                let global_variable = self.global_lookup_by_id.get(&(slot.binding_data.data as usize))
                    .ok_or_else(|| anyhow!("Failed to find global with index specified"))?;
                // Make sure the global variable has been initialized
                let current_value = global_variable.current_value.borrow().clone()
                    .ok_or_else(|| anyhow!("Attempt to read uninitialized global variable {}", global_variable.name))?;
                Ok(Some(GospelVMValue::Integer(current_value)))
            }
            GospelSlotBinding::PlatformConfigProperty => {
                if slot.binding_data.value_type != GospelValueType::Integer {
                    bail!("Invalid platform config property slot binding data, expected value type to be integer")
                }
                // For now all platform config variables are integers
                if slot.value_type != GospelValueType::Integer {
                    bail!("Slot value type is not compatible with global variable value type")
                }

                let config_property = GospelPlatformConfigProperty::from_repr(slot.binding_data.value_type as u8)
                    .ok_or_else(|| anyhow!("Unknown platform config property"))?;
                let resolved_value = self.resolve_platform_config_property(config_property);
                Ok(Some(GospelVMValue::Integer(resolved_value)))
            }
            GospelSlotBinding::TypeArgumentValue => {
                if slot.binding_data.value_type != GospelValueType::Integer {
                    bail!("Invalid template argument value slot binding data, expected value type to be integer")
                }
                let argument_index = slot.binding_data.data as usize;
                if argument_index >= type_definition.arguments.len() {
                    bail!("Invalid template argument index #{} (number of template arguments: {})", argument_index, type_definition.arguments.len());
                }
                if type_definition.arguments[argument_index].argument_type != slot.value_type {
                    bail!("Incompatible value type for slot and argument at index #{}", argument_index);
                }
                let resolved_value = if argument_index >= args.len() {
                    let static_value = type_definition.arguments[argument_index].default_value.clone()
                        .ok_or_else(|| anyhow!("Missing value for argument #{} with no default value provided", argument_index))?;
                    self.resolve_static_value(&static_value)?
                } else {
                    args[argument_index].clone()
                };
                if resolved_value.value_type() != type_definition.arguments[argument_index].argument_type {
                    bail!("Incompatible value type for argument type and provided value");
                }
                Ok(Some(resolved_value))
            }
        }
    }
    fn resolve_layout_internal(self: &Rc<Self>, index: u32, args: &Vec<GospelVMValue>) -> anyhow::Result<GospelTypeLayout> {
        if index as usize >= self.container.types.len() {
            bail!("Invalid type index #{} out of bounds (num types in container: {})", index, self.container.types.len());
        }
        let type_definition = &self.container.types[index as usize];

        // Construct a fresh VM state
        let mut vm_state = GospelVMExecutionState{
            target_triplet: &self.target_triplet,
            instructions: &type_definition.code,
            slot_definitions: &type_definition.slots,
            layout_builder: GospelTypeLayout::default(),
            slots: Vec::with_capacity(type_definition.slots.len()),
            referenced_strings: Vec::with_capacity(type_definition.referenced_strings.len()),
            stack: Vec::new(),
            current_instruction_index: 0,
            current_loop_jump_count: 0,
            max_stack_size: 256, // TODO: Make limits configurable
            max_loop_jumps: 8192,
        };

        // Populate slots with their initial values
        for slot_index in 0..type_definition.slots.len() {
            let slot_value = self.resolve_slot_binding(type_definition, &type_definition.slots[slot_index], args)
            .map_err(|x| {
                let slot_name = self.container.strings.get(type_definition.slots[slot_index].debug_name).unwrap_or("<invalid>");
                anyhow!("Failed to bind slot #{} ({}) value: {}", slot_index, slot_name.to_string(), x.to_string())
            })?;
            vm_state.slots.push(slot_value)
        }

        // Populate referenced strings
        for string_index in &type_definition.referenced_strings {
            vm_state.referenced_strings.push(self.container.strings.get(*string_index)?.to_string());
        }

        // Populate layout builder with metadata
        vm_state.layout_builder.name = self.container.strings.get(type_definition.type_name)?.to_string();
        vm_state.layout_builder.source_type = Some(GospelVMTypeReference{container: self.clone(), type_index: index});
        vm_state.layout_builder.source_args = Some(args.clone());

        // Run the VM to evaluate the type now. Note that this can give us a completely different type as well
        GospelVMExecutionState::run(&mut vm_state)
    }
}

/// VM state for the Gospel VM
/// Containers can be injected into the VM to register type definitions
/// Global variables can be defined to supply additional information to the type definitions.
/// Type definitions can be retrieved with find_type
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
            type_lookup_by_name: HashMap::new()
        };

        // Build lookup table for types by name, and create globals referenced by the container
        for type_index in 0..wrapped_container.types.len() {
            let type_name = wrapped_container.strings.get(wrapped_container.types[type_index].type_name)?;
            vm_container.type_lookup_by_name.insert(type_name.to_string(), type_index as u32);
        }
        for global_index in 0..wrapped_container.globals.len() {
            let global_name = wrapped_container.strings.get(wrapped_container.globals[global_index].name)?;
            let initial_value = wrapped_container.globals[global_index].default_value;

            let global_value = self.find_or_create_global(global_name, initial_value)?;
            vm_container.global_lookup_by_id.insert(global_index, global_value);
        }

        // Finally, add container to the mounted container list
        let wrapped_vm_container = Rc::new(vm_container);
        self.containers.push(wrapped_vm_container.clone());
        self.containers_by_name.insert(container_name, wrapped_vm_container.clone());

        Ok(wrapped_vm_container)
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

    /// Returns the type container by name
    pub fn find_named_container(&self, name: &str) -> Option<Rc<GospelVMContainer>> {
        self.containers_by_name.get(name).map(|x| x.clone())
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
