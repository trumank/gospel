use std::io::{Read, Write};
use anyhow::anyhow;
use strum_macros::{FromRepr};
use crate::bytecode::GospelInstruction;
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u32)]
pub enum GospelPlatform {
    Unknown = 0x00,
    Windows = 0x01,
    Linux = 0x02,
    Mac = 0x03,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u32)]
pub enum GospelArch {
    X64 = 0x00,
    ARM64 = 0x01,
    ARM64EC = 0x02,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u32)]
pub(crate) enum GospelPlatformConfigProperty {
    PlatformId = 0x00, // ID of the platform, one of the values of GospelPlatform
    PlatformWordSize = 0x01, // Size of the pointer for the platform, in bytes (8 for 64-bit platforms)
    PlatformArch = 0x02, // Architecture for the platform, one of the values of GospelArch
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelSlotBinding {
    None = 0x00, // no binding, initialized with zero value
    // Global variable bindings
    PlatformConfigProperty = 0x01, // platform config property by ID
    InputVariableValue = 0x02, // input variable value by name, name is stored in the string table at the index specified
    TypeInstanceSize = 0x03, // size of a type instance by ID
    TypeInstanceAlignment = 0x04, // alignment of a type instance by ID
    // Template argument bindings
    TypeArgumentTypeSize = 0x10, // size of the template type argument by index
    TypeArgumentTypeAlignment = 0x11, // alignment of the template type argument by index
    TypeArgumentIntegralValue = 0x12, // value of the template integral argument by index
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelSlotDefinition {
    pub binding: GospelSlotBinding,
    pub binding_value: u32,
}
impl Readable for GospelSlotDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_binding: u8 = stream.de()?;
        let binding = GospelSlotBinding::from_repr(raw_binding)
            .ok_or_else(|| anyhow!("Unknown slot binding value"))?;
        let binding_value: u32 = stream.de()?;
        Ok(Self{binding, binding_value})
    }
}
impl Writeable for GospelSlotDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(self.binding as u8))?;
        stream.ser(&self.binding_value)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelTypeArgumentType {
    Type = 0x00, // argument is a type (either a gospel type or an external type)
    Integer = 0x01, // argument is an integral value
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelTypeArgumentValueKind {
    TypeInstance = 0x00, // argument value 1 is an ID of a type instance, argument value 2 is unused
    TypeSizeAndAlignment = 0x01, // argument value 1 is a precomputed size and argument value 2 is an alignment of an external type
    Integer = 0x02, // argument value 1 is an integer, argument value 2 is unused
}

#[derive(Debug, PartialEq, Clone, Copy, Hash)]
pub(crate) struct GospelTypeArgumentValue {
    pub kind: GospelTypeArgumentValueKind,
    pub data: [u32; 2],
}
impl Readable for GospelTypeArgumentValue {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self>  {
        let raw_kind: u8 = stream.de()?;
        let kind = GospelTypeArgumentValueKind::from_repr(raw_kind)
            .ok_or_else(|| anyhow!("Unknown argument value kind"))?;
        let data: [u32; 2] = [stream.de()?, stream.de()?];
        Ok(Self{kind, data})
    }
}
impl Writeable for GospelTypeArgumentValue {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        let raw_kind = self.kind as u8;
        stream.ser(&raw_kind)?;
        stream.ser(&self.data[0])?;
        stream.ser(&self.data[1])?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelTypeArgumentDefinition {
    pub argument_name: u32, // name of the argument, index to string table
    pub argument_type: GospelTypeArgumentType, // type of the argument
    pub default_value: Option<GospelTypeArgumentValue>, // default value for the argument, if available
}
impl Readable for GospelTypeArgumentDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let argument_name: u32 = stream.de()?;
        let raw_argument_type: u8 = stream.de()?;
        let argument_type: GospelTypeArgumentType = GospelTypeArgumentType::from_repr(raw_argument_type)
            .ok_or_else(|| anyhow!("Unknown type argument type"))?;
        let default_value: Option<GospelTypeArgumentValue> = stream.de()?;
        Ok(Self{argument_name, argument_type, default_value})
    }
}
impl Writeable for GospelTypeArgumentDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.argument_name)?;
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
}
impl Readable for GospelTypeDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            type_name: stream.de()?,
            arguments: stream.de()?,
            slots: stream.de()?,
            code: stream.de()?,
        })
    }
}
impl Writeable for GospelTypeDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.type_name)?;
        stream.ser(&self.arguments)?;
        stream.ser(&self.slots)?;
        stream.ser(&self.code)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub(crate) struct GospelTypeInstance {
    pub type_index: u32, // index of the base type definition
    pub arguments: Vec<GospelTypeArgumentValue>, // argument values for type definition arguments
}
impl Readable for GospelTypeInstance {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            type_index: stream.de()?,
            arguments: stream.de()?,
        })
    }
}
impl Writeable for GospelTypeInstance {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.type_index)?;
        stream.ser(&self.arguments)?;
        Ok({})
    }
}
