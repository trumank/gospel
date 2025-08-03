use std::str::FromStr;
use strum_macros::{Display, EnumProperty, EnumString, FromRepr};
use std::string::ToString;
use anyhow::bail;
use serde::{Deserialize, Serialize};
use strum::EnumProperty;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, EnumProperty, Display, EnumString)]
#[repr(u8)]
pub enum GospelOpcode {
    // Basic opcodes
    Noop = 0x00, // ; ->
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    IntConstant = 0x01, // <imm>; -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "2"))]
    Dup = 0x02, // ; [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "2"))]
    Permute = 0x03, // ; [pop stack], [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "1"))]
    Pop = 0x04, // ; [pop stack] ->
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Equals = 0x05, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1"))]
    ReturnValue = 0x06, // [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    Call = 0x07, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    BindClosure = 0x08, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1"))]
    Abort = 0x09, // <imm>; ->
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Typeof = 0x10, // [pop stack] -> [push stack]
    // Logical opcodes
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    And = 0x20, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Or = 0x21, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Xor = 0x22, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Shl = 0x23, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Shr = 0x24, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    ReverseBits = 0x25, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Ez = 0x27, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Lz = 0x28, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Lez = 0x29, // ; [pop stack] -> [push stack]
    // Arithmetic opcodes
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Add = 0x30, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Sub = 0x31, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Mul = 0x32, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Div = 0x33, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Rem = 0x34, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Neg = 0x35, // ; [pop stack] -> [push stack]
    // Control flow opcodes
    #[strum(props(immediate_count = "1"))]
    Branch = 0x40, // <imm>; ->
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    Branchz = 0x41, // <imm>; [pop stack] ->
    // Data storage opcodes
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadSlot = 0x51, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    StoreSlot = 0x52, // <imm>; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    TakeSlot = 0x53, // <imm>; -> [push stack]
    // Type layout access opcodes
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetSize = 0x61, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetAlignment = 0x62, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetUnalignedSize = 0x63, // ; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutDoesMemberExist = 0x64, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetMemberOffset = 0x65, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetMemberSize = 0x66, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetMemberTypeLayout = 0x67, // <imm>; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutIsChildOf = 0x68, // [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutGetOffsetOfBase = 0x69, // [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutCreatePointer = 0x6A, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutIsPointer = 0x6B, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetPointerPointeeType = 0x6C, // ; [pop stack] -> [push stack]
    // Type layout modification opcodes
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    TypeLayoutAllocate = 0x70, // <imm>; -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutAlign = 0x71, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutPad = 0x72, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutDefineBaseClass = 0x73, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutDefineMember = 0x74, // <imm>; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutFinalize = 0x75, // [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "3", stack_out_count = "1"))]
    TypeLayoutDefineArrayMember = 0x76, // <imm>; [pop stack] [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeLayoutSetMetadata = 0x77, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeLayoutGetMetadata = 0x78, // ; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "3", stack_out_count = "1"))]
    TypeLayoutDefineBitfieldMember = 0x79, // <imm>; [pop stack] [pop stack] [pop stack] -> [push stack]
    // Array opcodes
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    ArrayGetLength = 0x80, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    ArrayGetItem = 0x81, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_out_count = "1"))]
    ArrayAllocate = 0x82, // ; -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    ArrayReserve = 0x83, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    ArrayPushItem = 0x84, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "3", stack_out_count = "1"))]
    ArrayInsertItem = 0x85, // ; [pop stack], [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    ArrayRemoveItem = 0x86, // ; [pop stack], [pop stack] -> [push stack]
    // Struct opcodes
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    StructAllocate = 0x90, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "1", stack_out_count = "1"))]
    StructGetLocalField = 0x92, // <imm> <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "2", stack_out_count = "1"))]
    StructSetLocalField = 0x93, // <imm> <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "1", stack_out_count = "1"))]
    StructGetNamedField = 0x94, // <imm> <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "2", stack_out_count = "1"))]
    StructSetNamedField = 0x95, // <imm> <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    StructIsStructOfType = 0x96, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "1", stack_out_count = "1"))]
    StructGetNamedTypedField = 0x97, // <imm> <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "2", stack_in_count = "2", stack_out_count = "1"))]
    StructSetNamedTypedField = 0x98, // <imm> <imm>; [pop stack], [pop stack] -> [push stack]
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub struct GospelInstructionEncoding {
    immediate_count: u8,
}

impl GospelInstructionEncoding {
    const MAX_IMMEDIATE_COUNT: usize = 4;
    pub fn from_opcode(opcode: GospelOpcode) -> GospelInstructionEncoding {
        let immediate_count = opcode.get_str("immediate_count").map(|x| u8::from_str(x).unwrap()).unwrap_or(0);
        assert!(immediate_count <= Self::MAX_IMMEDIATE_COUNT as u8);
        Self{immediate_count}
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct GospelInstruction {
    raw_opcode: u8,
    instruction_encoding: GospelInstructionEncoding,
    immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT]
}

impl GospelInstruction {
    pub fn raw_opcode(&self) -> u8 { self.raw_opcode }
    pub fn opcode(&self) -> Option<GospelOpcode> { GospelOpcode::from_repr(self.raw_opcode) }
    pub fn instruction_encoding(&self) -> GospelInstructionEncoding { self.instruction_encoding }
    pub fn immediate_operands(&self) -> &[u32] { &self.immediate_operands[0..(self.instruction_encoding.immediate_count as usize)] }
    pub fn immediate_operand_at(&self, index: usize) -> Option<u32> { if index < self.instruction_encoding.immediate_count as usize { Some(self.immediate_operands[index]) } else { None } }
    pub fn set_immediate_operand(&mut self, operand_index: usize, new_value: u32) -> anyhow::Result<()> {
        if operand_index >= self.instruction_encoding.immediate_count as usize {
            bail!("Operand index #{} out of bounds (number of operands: {})", operand_index, self.instruction_encoding.immediate_count);
        }
        self.immediate_operands[operand_index] = new_value;
        Ok({})
    }
    pub fn create(opcode: GospelOpcode, immediate_operands: &[u32]) -> anyhow::Result<GospelInstruction> {
        let instruction_encoding = GospelInstructionEncoding::from_opcode(opcode);
        if instruction_encoding.immediate_count as usize != immediate_operands.len() {
            bail!("Operand count mismatch for opcode {}: expected {} immediate operands, but {} operands were provided",
                   opcode.to_string(), instruction_encoding.immediate_count, immediate_operands.len());
        }
        let mut result_immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT] = [0; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT];
        for index in 0..immediate_operands.len() {
            result_immediate_operands[index] = immediate_operands[index];
        }
        Ok(Self{raw_opcode: opcode as u8, instruction_encoding, immediate_operands: result_immediate_operands })
    }
    pub fn create_raw(raw_opcode: u8, encoding: GospelInstructionEncoding, immediate_operands: &[u32]) -> anyhow::Result<GospelInstruction> {
        if encoding.immediate_count as usize != immediate_operands.len() {
            bail!("Operand count mismatch: expected {} immediate operands, but {} operands were provided",
                encoding.immediate_count, immediate_operands.len());
        }
        let mut result_immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT] = [0; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT];
        for index in 0..immediate_operands.len() {
            result_immediate_operands[index] = immediate_operands[index];
        }
        Ok(Self{raw_opcode, instruction_encoding: encoding, immediate_operands: result_immediate_operands })
    }
}
