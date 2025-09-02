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
    Int8Constant = 0x01, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    Int16Constant = 0x02, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    Int32Constant = 0x03, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "2", stack_out_count = "1"))]
    Int64Constant = 0x04, // <imm> <imm>; -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "2"))]
    Dup = 0x05, // ; [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "2"))]
    Permute = 0x06, // ; [pop stack], [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "1"))]
    Pop = 0x07, // ; [pop stack] ->
    #[strum(props(stack_in_count = "1"))]
    SetReturnValue = 0x08, // ; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    Call = 0x09, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1", stack_variable_input_count_immediate = "0"))]
    BindClosure = 0x0A, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1"))]
    RaiseException = 0x0B, // <imm>; ->
    Return = 0x0C, // ; ->
    #[strum(props(immediate_count = "1"))]
    PushExceptionHandler = 0xD, // <imm>; ->
    PopExceptionHandler = 0xE, // ; ->
    // Logical opcodes
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    And = 0x20, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Or = 0x21,  // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Xor = 0x22, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Shl = 0x23, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Shr = 0x24, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    ReverseBits = 0x25, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    Ez = 0x27,  // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    Lz = 0x28,  // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    Lez = 0x29, // <imm>; [pop stack] -> [push stack]
    // Arithmetic opcodes
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Add = 0x30, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Sub = 0x31, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Mul = 0x32, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Div = 0x33, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    Rem = 0x34, // <imm>; [pop stack], [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    Neg = 0x35, // <imm>; [pop stack] -> [push stack]
    // Control flow opcodes
    #[strum(props(immediate_count = "1"))]
    Branch = 0x40, // <imm>; ->
    #[strum(props(immediate_count = "2", stack_in_count = "1"))]
    Branchz = 0x41, // <imm> <imm>; [pop stack] ->
    // Data storage opcodes
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadArgumentValue = 0x50, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadSlot = 0x51, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    StoreSlot = 0x52, // <imm>; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    TakeSlot = 0x53, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadTargetProperty = 0x54, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadGlobalVariable = 0x55, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadFunctionClosure = 0x56, // <imm>; -> [push stack]
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
    #[strum(props(immediate_count = "1", stack_in_count = "2"))]
    TypeUDTAddBaseClass = 0x79, // <imm>; [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "2", stack_in_count = "3"))]
    TypeUDTAddField = 0x7B, // <imm> <imm>; [pop stack] [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "2", stack_in_count = "3"))]
    TypeUDTAddBitfield = 0x7C, // <imm> <imm>; [pop stack] [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "3", stack_in_count = "2", stack_variable_input_count_immediate = "2"))]
    TypeUDTAddVirtualFunction = 0x7D, // <imm> <imm> <imm>; [pop stack] x <imm1> [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "2"))]
    TypeUDTAttachMetadata = 0x7E, // ; [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "1"))]
    TypeFinalize = 0x7F, // [pop stack] ->
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
    #[strum(props(stack_out_count = "1"))]
    StructAllocate = 0x90, // ; -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    StructGetField = 0x94, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "2", stack_out_count = "1"))]
    StructSetField = 0x95, // <imm>; [pop stack], [pop stack] -> [push stack]
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
    TypeUDTCalculateBaseOffset = 0xA5, // ; [pop stack] [pop stack] -> [push stack]
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
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypePointerCreateReference = 0xB5, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypePointerIsReference = 0xB6, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeIsEnumType = 0xB7, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeEnumIsScopedEnum = 0xB8, // ; [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    TypeEnumGetUnderlyingType = 0xB9, // ; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    TypeEnumHasConstantByName = 0xBA, // <imm>; [pop stack] -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "2"))]
    TypeEnumConstantValueByName = 0xBB, // <imm>; [pop stack] -> [push stack] [push stack]
    // Type creation opcode extensions
    #[strum(props(stack_in_count = "2"))]
    TypeUDTSetMemberPackAlignment = 0xC0, // ; [pop stack] [pop stack] ->
    #[strum(props(stack_in_count = "1"))]
    TypeMarkPartial = 0xC1, // [pop stack] ->
    #[strum(props(immediate_count = "2", stack_out_count = "1"))]
    TypeEnumAllocate = 0xC2,  // <imm> <imm>; -> [push stack]
    #[strum(props(stack_in_count = "2"))]
    TypeEnumSetUnderlyingType = 0xC3, // ; [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "2", stack_in_count = "2"))]
    TypeEnumAddConstantWithValue = 0xC4, // <imm> <imm>; [pop stack] [pop stack] ->
    #[strum(props(immediate_count = "2", stack_in_count = "1"))]
    TypeEnumAddConstant = 0xC5, // <imm> <imm>; [pop stack] ->
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
