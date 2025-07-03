use std::io::{Read, Write};
use anyhow::anyhow;
use strum_macros::{Display, FromRepr};
use crate::bytecode::GospelInstruction;
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub enum GospelTargetArch {
    X86_64 = 0x00,
    ARM64 = 0x01,
    ARM64EC = 0x02,
}

/// Corresponds to <sys> in LLVM target triplet
/// Target system generally defines calling convention used and object file format
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub enum GospelTargetOS {
    None = 0x00,
    Win32 = 0x01,
    Linux = 0x02,
    Darwin = 0x03,
}

/// Corresponds to <env> in LLVM target triplet
/// Target env determines the ABI rules used for type layout calculation, for example semantics used for C++ class inheritance and exception handling
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub enum GospelTargetEnv {
    MSVC = 0x00,
    Gnu = 0x01,
    Macho = 0x02,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, Display)]
#[repr(u8)]
pub enum GospelValueType {
    Integer = 0x00,
    TypeReference = 0x01,
    TypeLayout = 0x02,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub enum GospelPlatformConfigProperty {
    TargetArch = 0x00, // target architecture (GospelTargetArch)
    TargetOS = 0x01, // target operating system (GospelTargetOS)
    TargetEnv = 0x02, // target environment (GospelTargetEnv)
    AddressSize = 0x03, // size of the address (a pointer) on the platform, in bytes (8 bytes for 64-bit platforms, 4 bytes for 32-bit platforms)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelStaticValueType {
    Integer = 0x00, // value is signed integer, interpret data as literal i32 value
    TypeReference = 0x01, // value is a type definition, interpret data as GospelTypeIndex
    StaticTypeInstance = 0x02, // value is a type layout for a static type instance, interpret data as static type index
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct GospelStaticValue {
    pub value_type: GospelValueType,
    pub static_type: GospelStaticValueType,
    pub data: u32,
}
impl Readable for GospelStaticValue {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self>  {
        let raw_value_type: u8 = stream.de()?;
        let value_type = GospelValueType::from_repr(raw_value_type).ok_or_else(|| anyhow!("Unknown value type"))?;
        let raw_static_type: u8 = stream.de()?;
        let static_type = GospelStaticValueType::from_repr(raw_static_type).ok_or_else(|| anyhow!("Unknown static value type"))?;
        let data: u32 = stream.de()?;
        Ok(Self{value_type, static_type, data})
    }
}
impl Writeable for GospelStaticValue {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(self.value_type as u8))?;
        stream.ser(&(self.static_type as u8))?;
        stream.ser(&self.data)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelSlotBinding {
    Uninitialized = 0x00, // slot is left uninitialized, attempting to read contents before writing them will result in an error
    StaticValue = 0x01, // initialized with static value
    PlatformConfigProperty = 0x02, // platform config property by ID (stored as integer static value)
    GlobalVariableValue = 0x03, // input variable value by name (index stored as integer static value)
    TypeArgumentValue = 0x04, // value of the type argument passed to the type definition
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelSlotDefinition {
    pub(crate) value_type: GospelValueType,
    pub(crate) binding: GospelSlotBinding,
    pub(crate) binding_data: GospelStaticValue,
    pub(crate) debug_name: u32,
}
impl Readable for GospelSlotDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_value_type: u8 = stream.de()?;
        let value_type = GospelValueType::from_repr(raw_value_type)
            .ok_or_else(|| anyhow!("Unknown slot value type"))?;
        let raw_binding: u8 = stream.de()?;
        let binding = GospelSlotBinding::from_repr(raw_binding)
            .ok_or_else(|| anyhow!("Unknown slot binding value"))?;
        let binding_data: GospelStaticValue = stream.de()?;
        let debug_name: u32 = stream.de()?;
        Ok(Self{value_type, binding, binding_data, debug_name})
    }
}
impl Writeable for GospelSlotDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(self.value_type as u8))?;
        stream.ser(&(self.binding as u8))?;
        stream.ser(&self.binding_data)?;
        stream.ser(&self.debug_name)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelTypeArgumentDefinition {
    pub argument_type: GospelValueType, // type of the argument
    pub default_value: Option<GospelStaticValue>, // default value for the argument, if available
}
impl Readable for GospelTypeArgumentDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_argument_type: u8 = stream.de()?;
        let argument_type = GospelValueType::from_repr(raw_argument_type)
            .ok_or_else(|| anyhow!("Unknown type argument type"))?;
        let default_value: Option<GospelStaticValue> = stream.de()?;
        Ok(Self{argument_type, default_value})
    }
}
impl Writeable for GospelTypeArgumentDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        let raw_argument_type = self.argument_type as u8;
        stream.ser(&raw_argument_type)?;
        stream.ser(&self.default_value)?;
        Ok({})
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GospelTypeDefinition {
    pub type_name: u32, // name of the type, index to string table
    pub arguments: Vec<GospelTypeArgumentDefinition>, // type arguments for this type
    pub slots: Vec<GospelSlotDefinition>, // slots to bind to the code
    pub code: Vec<GospelInstruction>, // bytecode for the VM
    pub referenced_strings: Vec<u32>, // indices of strings referenced by the bytecode
}
impl Readable for GospelTypeDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            type_name: stream.de()?,
            arguments: stream.de()?,
            slots: stream.de()?,
            code: stream.de()?,
            referenced_strings: stream.de()?,
        })
    }
}
impl Writeable for GospelTypeDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.type_name)?;
        stream.ser(&self.arguments)?;
        stream.ser(&self.slots)?;
        stream.ser(&self.code)?;
        stream.ser(&self.referenced_strings)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub(crate) struct GospelTypeIndex(u32);
impl GospelTypeIndex {
    const INDEX_SHIFT: u32 = 0;
    const INDEX_MASK: u32 = (1 << 31) - 1;
    const TYPE_SHIFT: u32 = 31;
    const TYPE_MASK: u32 = 1 << 0;

    pub(crate) fn raw_value(self) -> u32 { self.0 }
    pub(crate) fn create_raw(raw: u32) -> Self { Self(raw) }

    fn create(index: u32, kind: u32) -> Self {
        Self::create_raw(((index & Self::INDEX_MASK) << Self::INDEX_SHIFT) |
            ((kind & Self::TYPE_MASK) << Self::TYPE_SHIFT))
    }
    pub(crate) fn create_local(index: u32) -> Self { Self::create(index, 0) }
    pub(crate) fn create_external(index: u32) -> Self { Self::create(index, 1) }

    pub(crate) fn index(self) -> u32 {
        (self.0 >> Self::INDEX_SHIFT) & Self::INDEX_MASK
    }
    fn kind(self) -> u32 {
        (self.0 >> Self::TYPE_SHIFT) & Self::TYPE_MASK
    }
    pub(crate) fn is_external(self) -> bool { self.kind() == 1 }
}
impl Readable for GospelTypeIndex {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self(stream.de()?))
    }
}
impl Writeable for GospelTypeIndex {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.0)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub(crate) struct GospelStaticTypeInstance {
    pub type_index: GospelTypeIndex, // index of the base type definition
    pub arguments: Vec<GospelStaticValue>, // argument values for type definition arguments
}
impl Readable for GospelStaticTypeInstance {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            type_index: stream.de()?,
            arguments: stream.de()?,
        })
    }
}
impl Writeable for GospelStaticTypeInstance {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.type_index)?;
        stream.ser(&self.arguments)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub(crate) struct GospelExternalTypeReference {
    pub import_index: u32, // index of the container from imports from which the named type is imported
    pub type_name: u32, // name of the imported type, index to the string table string
}
impl Readable for GospelExternalTypeReference {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            import_index: stream.de()?,
            type_name: stream.de()?,
        })
    }
}
impl Writeable for GospelExternalTypeReference {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.import_index)?;
        stream.ser(&self.type_name)?;
        Ok({})
    }
}
