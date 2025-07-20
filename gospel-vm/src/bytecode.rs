use std::io::{Read, Write};
use std::str::FromStr;
use strum_macros::{Display, EnumProperty, EnumString, FromRepr};
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};
use std::string::ToString;
use anyhow::bail;
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
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    Call = 0x07, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
    #[strum(props(immediate_count = "1", stack_in_count = "1", stack_out_count = "1"))]
    BindClosure = 0x08, // <imm>; [pop stack] [pop stack] x <imm> -> [push stack]
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
    BranchIfNot = 0x41, // <imm>; [pop stack] ->
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
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct GospelInstructionEncoding(u8);

impl GospelInstructionEncoding {
    const IMMEDIATE_COUNT_BIT_SHIFT: u8 = 0;
    const IMMEDIATE_COUNT_BIT_COUNT: u8 = 2;
    const STACK_IN_BIT_SHIFT: u8 = Self::IMMEDIATE_COUNT_BIT_SHIFT + Self::IMMEDIATE_COUNT_BIT_COUNT;
    const STACK_IN_BIT_COUNT: u8 = 2;
    const STACK_OUT_BIT_SHIFT: u8 = Self::STACK_IN_BIT_SHIFT + Self::STACK_IN_BIT_COUNT;
    const STACK_OUT_BIT_COUNT: u8 = 2;
    const MAX_IMMEDIATE_COUNT: usize = (1 << Self::IMMEDIATE_COUNT_BIT_COUNT) - 1;

    pub fn raw(self) -> u8 { self.0 }
    pub fn from_raw(raw: u8) -> GospelInstructionEncoding {
        Self(raw)
    }
    pub fn from_components(immediate_count: usize, stack_in: usize, stack_out: usize) -> GospelInstructionEncoding {
        Self::from_raw(
        ((immediate_count as u8 & ((1 << Self::IMMEDIATE_COUNT_BIT_COUNT) - 1)) << Self::IMMEDIATE_COUNT_BIT_SHIFT) |
            ((stack_in as u8 & ((1 << Self::STACK_IN_BIT_COUNT) - 1)) << Self::STACK_IN_BIT_SHIFT) |
            ((stack_out as u8 & ((1 << Self::STACK_OUT_BIT_COUNT) - 1)) << Self::STACK_OUT_BIT_SHIFT)
        )
    }
    pub fn from_opcode(opcode: GospelOpcode) -> GospelInstructionEncoding {
        Self::from_components(
            opcode.get_str("immediate_count").map(|x| usize::from_str(x).unwrap()).unwrap_or(0),
            opcode.get_str("stack_in_count").map(|x| usize::from_str(x).unwrap()).unwrap_or(0),
            opcode.get_str("stack_out_count").map(|x| usize::from_str(x).unwrap()).unwrap_or(0),
        )
    }

    pub fn immediate_count(self) -> usize {
        ((self.0 >> Self::IMMEDIATE_COUNT_BIT_SHIFT) & ((1 << Self::IMMEDIATE_COUNT_BIT_COUNT) - 1)) as usize
    }
    pub fn stack_in_count(self) -> usize {
        ((self.0 >> Self::STACK_IN_BIT_SHIFT) & ((1 << Self::STACK_IN_BIT_COUNT) - 1)) as usize
    }
    pub fn stack_out_count(self) -> usize {
        ((self.0 >> Self::STACK_OUT_BIT_SHIFT) & ((1 << Self::STACK_OUT_BIT_COUNT) - 1)) as usize
    }
}

impl Readable for GospelInstructionEncoding {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(GospelInstructionEncoding::from_raw(stream.de()?))
    }
}
impl Writeable for GospelInstructionEncoding {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        let value = self.raw();
        stream.ser(&value)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub struct GospelInstruction {
    raw_opcode: u8,
    instruction_encoding: GospelInstructionEncoding,
    immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT]
}

impl GospelInstruction {
    pub fn raw_opcode(&self) -> u8 { self.raw_opcode }
    pub fn opcode(&self) -> Option<GospelOpcode> { GospelOpcode::from_repr(self.raw_opcode) }
    pub fn instruction_encoding(&self) -> GospelInstructionEncoding { self.instruction_encoding }
    pub fn immediate_operands(&self) -> &[u32] { &self.immediate_operands[0..self.instruction_encoding.immediate_count()] }
    pub  fn immediate_operand_at(&self, index: usize) -> Option<u32> { if index < self.instruction_encoding.immediate_count() { Some(self.immediate_operands[index]) } else { None } }

    pub fn create(opcode: GospelOpcode, immediate_operands: &[u32]) -> anyhow::Result<GospelInstruction> {
        let instruction_encoding = GospelInstructionEncoding::from_opcode(opcode);
        if instruction_encoding.immediate_count() != immediate_operands.len() {
            bail!("Operand count mismatch for opcode {}: expected {} immediate operands, but {} operands were provided",
                   opcode.to_string(), instruction_encoding.immediate_count(), immediate_operands.len());
        }
        let mut result_immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT] = [0; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT];
        for index in 0..immediate_operands.len() {
            result_immediate_operands[index] = immediate_operands[index];
        }
        Ok(Self{raw_opcode: opcode as u8, instruction_encoding, immediate_operands: result_immediate_operands })
    }
    pub fn create_raw(raw_opcode: u8, encoding: GospelInstructionEncoding, immediate_operands: &[u32]) -> anyhow::Result<GospelInstruction> {
        if encoding.immediate_count() != immediate_operands.len() {
            bail!("Operand count mismatch: expected {} immediate operands, but {} operands were provided",
                encoding.immediate_count(), immediate_operands.len());
        }
        let mut result_immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT] = [0; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT];
        for index in 0..immediate_operands.len() {
            result_immediate_operands[index] = immediate_operands[index];
        }
        Ok(Self{raw_opcode, instruction_encoding: encoding, immediate_operands: result_immediate_operands })
    }
}

impl Readable for GospelInstruction {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_opcode: u8 = stream.de()?;
        let instruction_encoding = GospelInstructionEncoding::from_raw(stream.de()?);
        let mut immediate_operands: [u32; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT] = [0; GospelInstructionEncoding::MAX_IMMEDIATE_COUNT];

        for immediate_operand_index in 0..instruction_encoding.immediate_count() {
            immediate_operands[immediate_operand_index] = stream.de()?;
        }
        Ok(Self::create_raw(raw_opcode, instruction_encoding, &immediate_operands[0..instruction_encoding.immediate_count()])?)
    }
}
impl Writeable for GospelInstruction {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.raw_opcode)?;
        stream.ser(&self.instruction_encoding.raw())?;
        for immediate_operand_index in 0..self.instruction_encoding.immediate_count() {
            stream.ser(&self.immediate_operands[immediate_operand_index])?;
        }
        Ok({})
    }
}
