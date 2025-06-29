use std::io::{Read, Write};
use anyhow::anyhow;
use strum_macros::FromRepr;
use crate::gospel_type::{GospelTypeDefinition, GospelTypeInstance};
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u32)]
pub(crate) enum GospelContainerVersion {
    Initial = 0x00, // initial version
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelContainerHeader {
    pub(crate) version: GospelContainerVersion,
    pub(crate) container_name: u32, // name of this container without extension, index to the string table
}
impl Readable for GospelContainerHeader {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_version: u32 = stream.de()?;
        let version = GospelContainerVersion::from_repr(raw_version)
            .ok_or_else(|| anyhow!("Unknown container header version"))?;
        let container_name: u32 = stream.de()?;
        Ok(Self{version, container_name})
    }
}
impl Writeable for GospelContainerHeader {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(self.version as u32))?;
        stream.ser(&self.container_name)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelGlobalDefinition {
    pub name: u32, // name of the global, index to the string table
    pub default_value: Option<i32>, // default value of the global, if present
}
impl Readable for GospelGlobalDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self>  {
        Ok(Self{
            name: stream.de()?,
            default_value: stream.de()?,
        })
    }
}
impl Writeable for GospelGlobalDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.name)?;
        stream.ser(&self.default_value)?;
        Ok({})
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GospelStringTable {
    pub(crate) data: Vec<String>,
}
impl Readable for GospelStringTable {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(GospelStringTable{
            data: stream.de()?,
        })
    }
}
impl Writeable for GospelStringTable {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.data)?;
        Ok({})
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GospelContainer {
    pub(crate) header: GospelContainerHeader,
    pub(crate) globals: Vec<GospelGlobalDefinition>,
    pub(crate) types: Vec<GospelTypeDefinition>,
    pub(crate) instances: Vec<GospelTypeInstance>,
    pub(crate) strings: GospelStringTable,
}
impl Readable for GospelContainer {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            header: stream.de()?,
            globals: stream.de()?,
            types: stream.de()?,
            instances: stream.de()?,
            strings: stream.de()?,
        })
    }
}
impl Writeable for GospelContainer {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.header)?;
        stream.ser(&self.globals)?;
        stream.ser(&self.types)?;
        stream.ser(&self.instances)?;
        stream.ser(&self.strings)?;
        Ok({})
    }
}
