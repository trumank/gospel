use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use anyhow::{anyhow, bail};
use strum_macros::Display;
use crate::bytecode::{GospelInstruction, GospelOpcode};
use crate::container::GospelContainer;
use crate::gospel_type::{GospelPlatformConfigProperty, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelStaticValueType, GospelTargetArch, GospelTargetEnv, GospelTargetOS, GospelFunctionDefinition, GospelFunctionIndex, GospelValueType};
use crate::writer::{GospelSourceFunctionReference, GospelSourceLazyValue, GospelSourceStaticValue};
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelBaseClassLayout {
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelMemberLayout {
    pub name: String,
    pub offset: usize,
    /// If this is a statically sized array, size of the array
    pub array_size: Option<usize>,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

/// Represents a fully resolved layout of a particular type
/// This exposes information such as the size of the type, its alignment, unaligned size,
/// and offsets, sizes and full type layouts of its members
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GospelTypeLayout {
    pub name: String,
    pub alignment: usize,
    pub unaligned_size: usize,
    pub size: usize,
    pub base_classes: Vec<GospelBaseClassLayout>,
    pub members: Vec<GospelMemberLayout>,
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
#[derive(Debug, Clone)]
pub struct GospelVMFunctionPointer {
    container: Rc<GospelVMContainer>,
    function_index: u32,
}
impl GospelVMFunctionPointer {
    pub fn pointer_equal(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.container, &other.container) && self.function_index == other.function_index
    }
}
impl Display for GospelVMFunctionPointer {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let container_name = self.container.container_name().unwrap_or("<unknown>");
        let function_name = self.function_name().unwrap_or("<unknown>");
        write!(f, "{}:{}", container_name, function_name)
    }
}
impl GospelVMFunctionPointer {
    /// Returns the type container which defines this type
    pub fn source_container(&self) -> Rc<GospelVMContainer> {
        self.container.clone()
    }
    /// Returns the name of the function
    pub fn function_name(&self) -> Option<&str> {
        self.container.get_function_name(self.function_index)
    }
    /// Attempts to execute this function and returns the result
    pub fn execute(&self, args: &Vec<GospelVMValue>) -> anyhow::Result<GospelVMValue> {
        self.container.execute_function_internal(self.function_index, args, 0)
    }
}

/// VM Value represents a value that VM bytecode can read and write
/// Currently supported value types are integers, function pointers and type layouts
/// Function pointers can be called to yield their return value
/// Values can be compared for equality, but values of certain types might never be equivalent (for example, unnamed type layouts are never equivalent, even to themselves)
#[derive(Debug, Clone, Display)]
pub enum GospelVMValue {
    #[strum(to_string = "Integer({0})")]
    Integer(i32), // signed 32-bit integer value
    #[strum(to_string = "FunctionPointer({0})")]
    FunctionPointer(GospelVMFunctionPointer), // definition of a type with no template arguments
    #[strum(to_string = "TypeLayout({0:#?})")]
    TypeLayout(GospelTypeLayout), // pre-computed type layout
}
impl GospelVMValue {
    pub fn value_type(&self) -> GospelValueType {
        match self {
            GospelVMValue::Integer(_) => { GospelValueType::Integer }
            GospelVMValue::FunctionPointer(_) => { GospelValueType::FunctionPointer }
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
            GospelVMValue::FunctionPointer(a) => match other {
                GospelVMValue::FunctionPointer(b) => { a.pointer_equal(b) }
                _ => false
            }
            GospelVMValue::TypeLayout(a) => match other {
                GospelVMValue::TypeLayout(b) => { a.eq(b) }
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
    target_triplet: &'a GospelVMTargetTriplet,
    function_return_type: GospelValueType,
    instructions: &'a Vec<GospelInstruction>,
    slot_definitions: &'a Vec<GospelSlotDefinition>,
    slots: Vec<Option<GospelVMValue>>,
    referenced_strings: Vec<String>,
    stack: Vec<GospelVMValue>,
    current_instruction_index: usize,
    current_loop_jump_count: usize,
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
    fn unwrap_value_as_function_pointer_checked(value: GospelVMValue) -> anyhow::Result<GospelVMFunctionPointer> {
        match value {
            GospelVMValue::FunctionPointer(unwrapped) => { Ok(unwrapped) }
            _ => bail!("Expected function pointer, got value of different type")
        }
    }
    fn validate_type_layout_complete(value: &GospelVMValue) -> anyhow::Result<()> {
        if let GospelVMValue::TypeLayout(type_layout) = value {
            if type_layout.size == 0 {
                bail!("Expected a complete type layout value, but got an incomplete type layout. Non-finalized type layouts cannot be read");
            }
        }
        Ok({})
    }
    fn unwrap_value_as_complete_type_layout_checked(value: GospelVMValue) -> anyhow::Result<GospelTypeLayout> {
        match value {
            GospelVMValue::TypeLayout(unwrapped) => {
                if unwrapped.size == 0 {
                    bail!("Expected a complete type layout value, but got an incomplete type layout. Non-finalized type layouts cannot be read");
                }
                Ok(unwrapped)
            }
            _ => bail!("Expected type layout value, got value of a different type")
        }
    }
    fn unwrap_value_as_partial_type_layout_checked(value: GospelVMValue) -> anyhow::Result<GospelTypeLayout> {
        match value {
            GospelVMValue::TypeLayout(unwrapped) => {
                if unwrapped.size != 0 {
                    bail!("Expected a partial type layout, but got a complete type layout. Finalized type layouts cannot be written");
                }
                Ok(unwrapped)
            }
            _ => bail!("Expected type layout value, got value of a different type")
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
        let type_layout = Self::unwrap_value_as_complete_type_layout_checked(self.pop_stack_check_underflow()?)?;

        let result_member = type_layout.find_named_member(member_name.as_str()).ok_or_else(|| {
            anyhow!("Failed to find member named {} inside type {}", member_name.clone(), type_layout.name.clone())
        })?;
        op(result_member);
        Ok({})
    }
    fn run(state: &mut GospelVMExecutionState) -> anyhow::Result<GospelVMValue> {
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

                    // This is a bit too aggressive, but we do not want incomplete type values to leak any information about their contents until they are finalized
                    Self::validate_type_layout_complete(&stack_value_a)?;
                    Self::validate_type_layout_complete(&stack_value_b)?;

                    let result = stack_value_a == stack_value_b;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::ReturnValue => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    if stack_value.value_type() != state.function_return_type {
                        bail!("Incompatible return value type");
                    }
                    if !state.stack.is_empty() {
                        bail!("Stack not empty upon function return");
                    }
                    return Ok(stack_value)
                }
                GospelOpcode::Call => {
                    let number_of_arguments = Self::immediate_value_checked(instruction, 0)? as usize;
                    let function_pointer = Self::unwrap_value_as_function_pointer_checked(state.pop_stack_check_underflow()?)?;
                    let mut function_arguments: Vec<GospelVMValue> = Vec::with_capacity(number_of_arguments);
                    for _ in 0..number_of_arguments {
                        function_arguments.push(state.pop_stack_check_underflow()?);
                    }
                    if state.recursion_counter >= state.max_recursion_depth {
                        bail!("Recursion limit reached");
                    }
                    let return_value = function_pointer.container.execute_function_internal(function_pointer.function_index, &function_arguments, state.recursion_counter).map_err(|err| {
                        let function_name = function_pointer.function_name().unwrap_or("<unknown>");
                        anyhow!("Failed to call function {}: {}", function_name.to_string(), err.to_string())
                    })?;
                    state.push_stack_check_overflow(return_value)?;
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
                // Type layout access opcodes
                GospelOpcode::TypeLayoutGetSize => {
                    let type_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.size as i32))?;
                }
                GospelOpcode::TypeLayoutGetAlignment => {
                    let type_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.alignment as i32))?;
                }
                GospelOpcode::TypeLayoutGetUnalignedSize => {
                    let type_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(type_layout.unaligned_size as i32))?;
                }
                GospelOpcode::TypeLayoutDoesMemberExist => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;
                    let type_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;

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
                    let child_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    let parent_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    let result = child_layout.get_base_offset(&parent_layout).is_some();
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                GospelOpcode::TypeLayoutGetOffsetOfBase => {
                    let child_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    let parent_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    let result = child_layout.get_base_offset(&parent_layout)
                        .ok_or_else(|| anyhow!("Type {} is not a base of type {}", child_layout.name.clone(), parent_layout.name.clone()))?;
                    state.push_stack_check_overflow(GospelVMValue::Integer(result as i32))?;
                }
                // Structure opcodes
                GospelOpcode::TypeLayoutAllocate => {
                    let type_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
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
                    let alignment = Self::unwrap_value_as_int_checked(stack_value)? as usize;
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    if alignment == 0 {
                        bail!("Invalid alignment of zero (division by zero)");
                    }
                    layout_builder.alignment = max(layout_builder.alignment, alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, alignment);
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutPad => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let padding_bytes = Self::unwrap_value_as_int_checked(stack_value)? as usize;
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    layout_builder.unaligned_size += padding_bytes;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineBaseClass => {
                    let stack_value = state.pop_stack_check_underflow()?;
                    let base_class_layout = Self::unwrap_value_as_complete_type_layout_checked(stack_value)?;
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    // Make sure the alignment requirement is met for the base class
                    layout_builder.alignment = max(layout_builder.alignment, base_class_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, base_class_layout.alignment);

                    // Actual class size differs depending on ABI used, on MSVC aligned base class size is used, while on GNU/Darwin
                    // unaligned class size is used, saving some space on derived types that are inherited from base classes ending with alignment padding
                    let actual_base_class_size = if state.target_triplet.uses_aligned_base_class_size() {
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
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let stack_value = state.pop_stack_check_underflow()?;
                    let member_layout = Self::unwrap_value_as_complete_type_layout_checked(stack_value)?;
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    // Make sure the alignment requirement is met for the member
                    layout_builder.alignment = max(layout_builder.alignment, member_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, member_layout.alignment);

                    let actual_size = member_layout.size;
                    layout_builder.members.push(GospelMemberLayout{
                        name: member_name,
                        offset: layout_builder.unaligned_size,
                        array_size: None,
                        actual_size,
                        layout: member_layout,
                    });
                    layout_builder.unaligned_size += actual_size;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutDefineArrayMember => {
                    let member_name_index = Self::immediate_value_checked(instruction, 0)? as usize;
                    let member_name = state.copy_referenced_string_checked(member_name_index)?;

                    let array_size = Self::unwrap_value_as_int_checked(state.pop_stack_check_underflow()?)? as usize;
                    let member_layout = Self::unwrap_value_as_complete_type_layout_checked(state.pop_stack_check_underflow()?)?;
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    // Make sure the alignment requirement is met for the member
                    layout_builder.alignment = max(layout_builder.alignment, member_layout.alignment);
                    layout_builder.unaligned_size = Self::align_value(layout_builder.unaligned_size, member_layout.alignment);

                    let actual_size = member_layout.size * array_size;
                    let array_member_name = format!("{}[{}]", member_name, array_size);
                    layout_builder.members.push(GospelMemberLayout{
                        name: array_member_name,
                        offset: layout_builder.unaligned_size,
                        array_size: Some(array_size),
                        actual_size,
                        layout: member_layout,
                    });
                    layout_builder.unaligned_size += actual_size;
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
                GospelOpcode::TypeLayoutFinalize => {
                    let mut layout_builder = Self::unwrap_value_as_partial_type_layout_checked(state.pop_stack_check_underflow()?)?;

                    // Make sure the size is at least one byte, and calculate the aligned size from unaligned size
                    if layout_builder.unaligned_size == 0 {
                        layout_builder.unaligned_size = 1;
                    }
                    layout_builder.size = Self::align_value(layout_builder.unaligned_size, layout_builder.alignment);
                    state.push_stack_check_overflow(GospelVMValue::TypeLayout(layout_builder))?;
                }
            };
        }
        // Function should always at the very least return a value, empty function code or fall through without return is an error
        bail!("Function failed to return a value");
    }
}

#[derive(Debug)]
pub struct GospelVMContainer {
    target_triplet: GospelVMTargetTriplet,
    container: Rc<GospelContainer>,
    external_references: Vec<Rc<GospelVMContainer>>,
    global_lookup_by_id: HashMap<usize, Rc<GospelGlobalStorage>>,
    function_lookup_by_name: HashMap<String, u32>,
    name_lookup_by_function: HashMap<u32, u32>,
}
impl GospelVMContainer {
    /// Returns the name of this type container
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.container.container_name()
    }
    /// Attempts to find a function with the given name in this container and returns a reference to it
    pub fn find_named_function(self: &Rc<Self>, name: &str) -> Option<GospelVMFunctionPointer> {
        self.function_lookup_by_name.get(name).map(|type_index| GospelVMFunctionPointer {
            container: self.clone(), function_index: *type_index })
    }
    fn get_function_name(&self, function_index: u32) -> Option<&str> {
        self.name_lookup_by_function.get(&function_index)
            .and_then(|x| self.container.strings.get(*x).ok())
    }
    fn resolve_function_index(self: &Rc<Self>, function_index: GospelFunctionIndex) -> anyhow::Result<GospelVMFunctionPointer> {
        if function_index.is_external() {
            if function_index.index() as usize >= self.container.external_functions.len() {
                bail!("Invalid external function index #{} out of bounds (num external function references in container: {})", function_index.index(), self.container.external_functions.len());
            }
            let external_function = &self.container.external_functions[function_index.index() as usize];
            if external_function.import_index as usize >= self.external_references.len() {
                bail!("Invalid external container reference index #{} out of bounds (num external container references: {})", external_function.import_index, self.external_references.len());
            }
            let source_container = &self.external_references[external_function.import_index as usize];
            let type_name = self.container.strings.get(external_function.function_name)?;
            return source_container.find_named_function(type_name)
                .ok_or_else(|| { anyhow!("Imported named function {} does not exist in container {}", self.container_name().unwrap(), type_name.to_string()) });
        }
        Ok(GospelVMFunctionPointer { container: self.clone(), function_index: function_index.index() })
    }
    fn resolve_lazy_value(self: &Rc<Self>, index: u32, recursion_counter: usize) -> anyhow::Result<GospelVMValue> {
        if index as usize >= self.container.lazy_values.len() {
            bail!("Invalid lazy value index #{} out of bounds (num static type instances in container: {})", index, self.container.lazy_values.len());
        }
        let lazy_value = &self.container.lazy_values[index as usize];
        let type_reference = self.resolve_function_index(lazy_value.function_index)?;
        type_reference.container.execute_function_static(type_reference.function_index, &lazy_value.arguments, recursion_counter)
    }
    fn resolve_static_value(self: &Rc<Self>, value: &GospelStaticValue, recursion_counter: usize) -> anyhow::Result<GospelVMValue> {
        match value.static_type {
            GospelStaticValueType::Integer => {
                if value.value_type != GospelValueType::FunctionPointer {
                    bail!("Incompatible integer static initializer with a value type that is not an integer");
                }
                Ok(GospelVMValue::Integer(value.data as i32))
            }
            GospelStaticValueType::FunctionIndex => {
                if value.value_type != GospelValueType::FunctionPointer {
                    bail!("Incompatible function index static initializer with a value type that is not a function pointer");
                }
                let function_index = GospelFunctionIndex::create_raw(value.data);
                let reference = self.resolve_function_index(function_index)?;
                Ok(GospelVMValue::FunctionPointer(reference))
            }
            GospelStaticValueType::LazyValue => {
                let resolved_value = self.resolve_lazy_value(value.data, recursion_counter)?;
                if resolved_value.value_type() != value.value_type {
                    bail!("Incompatible lazy value initializer yielded value type different from the value type specified");
                }
                Ok(resolved_value)
            }
            GospelStaticValueType::GlobalVariableValue => {
                let global_variable = self.global_lookup_by_id.get(&(value.data as usize))
                    .ok_or_else(|| anyhow!("Failed to find global with index specified"))?;
                // Make sure the global variable has been initialized
                let current_value = global_variable.current_value.borrow().clone()
                    .ok_or_else(|| anyhow!("Attempt to read uninitialized global variable {}", global_variable.name))?;
                Ok(GospelVMValue::Integer(current_value))
            }
            GospelStaticValueType::PlatformConfigProperty => {
                let config_property = GospelPlatformConfigProperty::from_repr(value.data as u8)
                    .ok_or_else(|| anyhow!("Unknown platform config property"))?;
                let resolved_value = self.target_triplet.resolve_platform_config_property(config_property);
                Ok(GospelVMValue::Integer(resolved_value))
            }
        }
    }
    fn execute_function_static(self: &Rc<Self>, index: u32, args: &Vec<GospelStaticValue>, recursion_counter: usize) -> anyhow::Result<GospelVMValue> {
        let mut resolved_args: Vec<GospelVMValue> = Vec::new();
        for argument_index in 0..args.len() {
            let resolved_value = self.resolve_static_value(&args[argument_index], recursion_counter)
                .map_err(|x| anyhow!("Failed to resolve template argument #{} value: {}", argument_index, x.to_string()))?;
            resolved_args.push(resolved_value)
        }
        self.execute_function_internal(index, &resolved_args, recursion_counter)
    }
    fn resolve_slot_binding(self: &Rc<Self>, type_definition: &GospelFunctionDefinition, slot: &GospelSlotDefinition, args: &Vec<GospelVMValue>, recursion_counter: usize) -> anyhow::Result<Option<GospelVMValue>> {
        match slot.binding {
            GospelSlotBinding::StaticValue => {
                if let Some(static_value) = slot.static_value {
                    let resolved_value = self.resolve_static_value(&static_value, recursion_counter)?;
                    if slot.value_type != resolved_value.value_type() {
                        bail!("Slot value type is not compatible with static value type specified")
                    }
                    Ok(Some(resolved_value))
                } else { Ok(None) }
            }
            GospelSlotBinding::ArgumentValue => {
                if slot.argument_index as usize >= type_definition.arguments.len() {
                    bail!("Invalid template argument index #{} (number of template arguments: {})", slot.argument_index, type_definition.arguments.len());
                }
                if type_definition.arguments[slot.argument_index as usize].argument_type != slot.value_type {
                    bail!("Incompatible value type for slot and argument at index #{}", slot.argument_index);
                }
                let resolved_value = if slot.argument_index as usize >= args.len() {
                    let static_value = type_definition.arguments[slot.argument_index as usize].default_value.clone()
                        .ok_or_else(|| anyhow!("Missing value for argument #{} with no default value provided", slot.argument_index))?;
                    self.resolve_static_value(&static_value, recursion_counter)?
                } else {
                    args[slot.argument_index as usize].clone()
                };
                if resolved_value.value_type() != type_definition.arguments[slot.argument_index as usize].argument_type {
                    bail!("Incompatible value type for argument type and provided value");
                }
                Ok(Some(resolved_value))
            }
        }
    }
    fn execute_function_internal(self: &Rc<Self>, index: u32, args: &Vec<GospelVMValue>, recursion_counter: usize) -> anyhow::Result<GospelVMValue> {
        if index as usize >= self.container.functions.len() {
            bail!("Invalid function index #{} out of bounds (num functions in container: {})", index, self.container.functions.len());
        }
        let function_definition = &self.container.functions[index as usize];

        // Construct a fresh VM state
        let mut vm_state = GospelVMExecutionState{
            target_triplet: &self.target_triplet,
            function_return_type: function_definition.return_value_type,
            instructions: &function_definition.code,
            slot_definitions: &function_definition.slots,
            slots: Vec::with_capacity(function_definition.slots.len()),
            referenced_strings: Vec::with_capacity(function_definition.referenced_strings.len()),
            stack: Vec::new(),
            current_instruction_index: 0,
            current_loop_jump_count: 0,
            recursion_counter,
            max_stack_size: 256, // TODO: Make limits configurable
            max_loop_jumps: 8192,
            max_recursion_depth: 128,
        };

        // Populate slots with their initial values
        for slot_index in 0..function_definition.slots.len() {
            let slot_value = self.resolve_slot_binding(function_definition, &function_definition.slots[slot_index], args, recursion_counter)
            .map_err(|x| anyhow!("Failed to bind slot #{} value: {}", slot_index, x.to_string()))?;
            vm_state.slots.push(slot_value)
        }

        // Populate referenced strings
        for string_index in &function_definition.referenced_strings {
            vm_state.referenced_strings.push(self.container.strings.get(*string_index)?.to_string());
        }

        // Run the VM now to calculate the result of the function
        GospelVMExecutionState::run(&mut vm_state)
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
            name_lookup_by_function: HashMap::new(),
        };

        // Build lookup table for functions by name, and create globals referenced by the container
        for function_name_pair in &wrapped_container.function_names {
            let function_name = wrapped_container.strings.get(function_name_pair.function_name)?;
            vm_container.function_lookup_by_name.insert(function_name.to_string(), function_name_pair.function_index);
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
    pub fn find_function_by_reference(&self, reference: &GospelSourceFunctionReference, context: &Option<Rc<GospelVMContainer>>) -> Option<GospelVMFunctionPointer> {
        match reference {
            GospelSourceFunctionReference::LocalFunction{function_name} => {
                context.as_ref().and_then(|container| container.find_named_function(function_name.as_str()))
            }
            GospelSourceFunctionReference::ExternalFunction {function_name, container_name} => {
                self.find_named_container(container_name.as_str()).and_then(|container| container.find_named_function(function_name.as_str()))
            }
        }
    }

    /// Allows evaluating a source value without building a container first (REPL-like API)
    pub fn eval_source_value(&self, value: &GospelSourceStaticValue, context: &Option<Rc<GospelVMContainer>>) -> anyhow::Result<GospelVMValue> {
        match value {
            GospelSourceStaticValue::FunctionId(function_reference) => {
                self.find_function_by_reference(&function_reference, context)
                    .map(|function_pointer| GospelVMValue::FunctionPointer(function_pointer))
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
            GospelSourceStaticValue::LazyValue(lazy_value) => {
                self.eval_lazy_value(lazy_value, context)
            }
        }
    }

    /// Allows evaluating a source lazy value without building a container first (REPL-like API)
    pub fn eval_lazy_value(&self, value: &GospelSourceLazyValue, context: &Option<Rc<GospelVMContainer>>) -> anyhow::Result<GospelVMValue> {
        let function_pointer = self.find_function_by_reference(&value.function_reference, context)
            .ok_or_else(|| anyhow!("Failed to find function {} to evaluate the lazy value", value.function_reference))?;

        let mut compiled_function_arguments: Vec<GospelVMValue> = Vec::with_capacity(value.arguments.len());
        for source_argument in &value.arguments {
            let argument_value = self.eval_source_value(source_argument, context)?;
            compiled_function_arguments.push(argument_value);
        }
        let eval_result = function_pointer.execute(&compiled_function_arguments)?;
        if eval_result.value_type() != value.return_value_type {
            bail!("Function returned value of incompatible type {} (expected: {})", eval_result.value_type(), value.return_value_type);
        }
        Ok(eval_result)
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
