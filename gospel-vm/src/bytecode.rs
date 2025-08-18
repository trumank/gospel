use std::str::FromStr;
use strum::{Display, EnumProperty, EnumString, FromRepr};
use std::string::ToString;
use anyhow::bail;
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, EnumProperty, Display, EnumString, Serialize, Deserialize)]
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
    #[strum(props(stack_in_count = "1"))]
    SetReturnValue = 0x05, // ; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    Call = 0x06, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    BindClosure = 0x07, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1"))]
    Abort = 0x08, // <imm>; ->
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Typeof = 0x09, // ; [pop stack] -> [push stack]
    Return = 0x0A, // ; ->
    // #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "2", stack_variable_input_count_immediate = "0"))]
    PCall = 0x0B, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack], [push stack]
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
    // Type access opcodes
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeIsSameType = 0x60, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeGetBaseType = 0x61, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsPrimitiveType = 0x63, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsPointerType = 0x64, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsArrayType = 0x65, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsFunctionType = 0x66, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsUDTType = 0x67, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypePointerGetPointeeType = 0x68, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeArrayGetElementType = 0x69, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeArrayGetLength = 0x6A, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeUDTIsBaseClassOf = 0x6B, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTHasField = 0x6C, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTTypeofField = 0x6D, // <imm>; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTGetMetadata = 0x6E, // ; [pop stack] -> [push stack]
    // Type creation opcodes
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeAddConstantQualifier = 0x70, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeAddVolatileQualifier = 0x71, // ; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    TypePrimitiveCreate = 0x72, // <imm>; -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypePointerCreate = 0x73, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeArrayCreate = 0x74, // ; [pop stack] [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    TypeFunctionCreateGlobal = 0x75, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    TypeFunctionCreateMember = 0x76, // <imm>; [pop stack] [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "2", stack_out_count = "1"))]
    TypeUDTAllocate = 0x77, // <imm> <imm>; -> [push stack]
    #[strum(props(stack_in_count = "2"))]
    TypeUDTSetUserAlignment = 0x78, // ; [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "2"))]
    TypeUDTAddBaseClass = 0x79, // ; [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "2"))]
    TypeUDTAddField = 0x7A, // <imm>; [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "3"))]
    TypeUDTAddFieldWithUserAlignment = 0x7B, // <imm>; [pop stack] [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "3"))]
    TypeUDTAddBitfield = 0x7C, // <imm>; [pop stack] [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    TypeUDTAddVirtualFunction = 0x7D, // <imm>; [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "2"))]
    TypeUDTAttachMetadata = 0x7E, // ; [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "1"))]
    TypeUDTFinalize = 0x7F, // [pop stack] ->
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
    // Type layout calculation opcodes
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeCalculateSize = 0xA0, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeCalculateAlignment = 0xA1, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTCalculateUnalignedSize = 0xA2, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTHasVTable = 0xA3, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "3"))]
    TypeUDTCalculateVTableSizeAndOffset = 0xA4, // [pop stack] -> [push stack] [push stack] [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeUDTCalculateBaseOffset = 0xA5, // [pop stack] [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "2"))]
    TypeUDTCalculateVirtualFunctionOffset = 0xA6, // <imm>; [pop stack] -> [push stack] [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeUDTCalculateFieldOffset = 0xA7, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "3"))]
    TypeUDTCalculateBitfieldOffsetBitOffsetAndBitWidth = 0xA8, // <imm>; [pop stack] -> [push stack] [push stack] [push stack]
    // Type access opcode extensions
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeFunctionIsMemberFunction = 0xB0, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeFunctionGetThisType = 0xB1, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeFunctionGetArgumentCount = 0xB2, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeFunctionGetReturnValueType = 0xB3, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    TypeFunctionGetArgumentType = 0xB4, // ; [pop stack] [pop stack] -> [push stack]
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
    opcode: GospelOpcode,
    instruction_encoding: GospelInstructionEncoding,
    immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT]
}

impl GospelInstruction {
    pub fn opcode(&self) -> GospelOpcode { self.opcode }
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
        Ok(Self{opcode, instruction_encoding, immediate_operands: result_immediate_operands })
    }
}
