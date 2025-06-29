use std::io::{Read, Write};
use strum_macros::{Display, EnumProperty, FromRepr};
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};
use std::string::ToString;
use strum::EnumProperty;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, EnumProperty, Display)]
#[repr(u8)]
pub enum GospelOpcode {
    // Basic opcodes
    Noop = 0x00, // ; ->
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    Constant = 0x01, // <imm>; -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "2"))]
    Dup = 0x02, // ; [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "2"))]
    Permute = 0x03, // ; [pop stack], [pop stack] -> [push stack], [push stack]
    #[strum(props(stack_in_count = "1"))]
    Pop = 0x04, // ; [pop stack] ->
    // Structure opcodes
    #[strum(props(stack_in_count = "1"))]
    Align = 0x10, // ; [pop stack] ->
    #[strum(props(stack_in_count = "1"))]
    Pad = 0x11, // ; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    BaseClass = 0x12, // <imm>; [pop stack] ->
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    Member = 0x13, // <imm>; [pop stack] ->
    // Logical opcodes
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    And = 0x20, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Or = 0x21, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Xor = 0x22, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Flip = 0x23, // ; [pop stack], [pop stack] -> [push stack]
    // Arithmetic opcodes
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Add = 0x30, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Sub = 0x31, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "2", stack_out_count = "1"))]
    Mul = 0x32, // ; [pop stack], [pop stack] -> [push stack]
    #[strum(props(stack_in_count = "1", stack_out_count = "1"))]
    Neg = 0x33, // ; [pop stack] -> [push stack]
    // Control flow opcodes
    #[strum(props(immediate_count = "1"))]
    Branch = 0x40, // <imm>; ->
    #[strum(props(immediate_count = "1", stack_in_count = "1"))]
    BranchIfNot = 0x41, // <imm>; [pop stack] ->
    // Data storage opcodes
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    LoadSlot = 0x51, // <imm>; -> [push stack]
    #[strum(props(immediate_count = "1", stack_out_count = "1"))]
    StoreSlot = 0x52, // <imm>; -> [push stack]
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
    fn from_components(immediate_count: usize, stack_in: usize, stack_out: usize) -> GospelInstructionEncoding {
        Self::from_raw(
        ((immediate_count as u8 & ((1 << Self::IMMEDIATE_COUNT_BIT_COUNT) - 1)) << Self::IMMEDIATE_COUNT_BIT_SHIFT) |
            ((stack_in as u8 & ((1 << Self::STACK_IN_BIT_COUNT) - 1)) << Self::STACK_IN_BIT_SHIFT) |
            ((stack_out as u8 & ((1 << Self::STACK_OUT_BIT_COUNT) - 1)) << Self::STACK_OUT_BIT_SHIFT)
        )
    }
    pub fn from_opcode(opcode: GospelOpcode) -> GospelInstructionEncoding {
        Self::from_components(
            opcode.get_int("immediate_count").unwrap_or(0) as usize,
            opcode.get_int("stack_in_count").unwrap_or(0) as usize,
            opcode.get_int("stack_out_count").unwrap_or(0) as usize,
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
    fn raw_opcode(&self) -> u8 { self.raw_opcode }
    fn opcode(&self) -> Option<GospelOpcode> { GospelOpcode::from_repr(self.raw_opcode) }
    fn instruction_encoding(&self) -> GospelInstructionEncoding { self.instruction_encoding }
    fn immediate_operands(&self) -> &[u32] { &self.immediate_operands[0..self.instruction_encoding.immediate_count()] }
    fn immediate_operand_at(&self, index: usize) -> Option<u32> { if index < self.instruction_encoding.immediate_count() { Some(self.immediate_operands[index]) } else { None } }

    pub fn create(opcode: GospelOpcode, immediate_operands: &[u32]) -> GospelInstruction {
        let instruction_encoding = GospelInstructionEncoding::from_opcode(opcode);
        assert_eq!(instruction_encoding.immediate_count(), immediate_operands.len(), "Operand count mismatch for opcode {}: expected {} immediate operands, but {} operands were provided",
                   opcode.to_string(), instruction_encoding.immediate_count(), immediate_operands.len());
        Self{raw_opcode: opcode as u8, instruction_encoding, immediate_operands: immediate_operands.try_into().unwrap() }
    }
    pub fn create_raw(raw_opcode: u8, encoding: GospelInstructionEncoding, immediate_operands: &[u32]) -> GospelInstruction {
        assert_eq!(encoding.immediate_count(), immediate_operands.len(), "Operand count mismatch: expected {} immediate operands, but {} operands were provided",
                   encoding.immediate_count(), immediate_operands.len());
        Self{raw_opcode, instruction_encoding: encoding, immediate_operands: immediate_operands.try_into().unwrap() }
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
        Ok(Self::create_raw(raw_opcode, instruction_encoding, &immediate_operands))
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
