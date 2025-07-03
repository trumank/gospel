use std::io::{Cursor, Read, Write};
use anyhow::{anyhow, bail};
use strum_macros::FromRepr;
use crate::gospel_type::{GospelExternalTypeReference, GospelStaticTypeInstance, GospelTypeDefinition};
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default, FromRepr)]
#[repr(u32)]
pub(crate) enum GospelContainerVersion {
    #[default]
    Initial = 0x00, // initial version
}
impl GospelContainerVersion {
    pub(crate) fn current_version() -> GospelContainerVersion {
        GospelContainerVersion::Initial
    }
}

#[derive(Debug, Clone, Copy, Default)]
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

#[derive(Debug, Clone, Default)]
pub(crate) struct GospelStringTable {
    data: Vec<String>,
}
impl GospelStringTable {
    pub(crate) fn create(data: Vec<String>) -> Self {
        Self{data}
    }
    pub(crate) fn store(&mut self, string: String) -> u32 {
        let current_index = self.data.len() as u32;
        self.data.push(string);
        current_index
    }
    pub(crate) fn get(&self, index: u32) -> anyhow::Result<&str> {
        if index as usize >= self.data.len() {
            bail!("Invalid string table index #{} out of bounds (number of strings: {})", index, self.data.len());
        }
        Ok(self.data[index as usize].as_str())
    }
}

impl Readable for GospelStringTable {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self::create(stream.de()?))
    }
}
impl Writeable for GospelStringTable {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.data)?;
        Ok({})
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GospelContainerImport {
    pub(crate) container_name: u32, // name of the imported container, index to the string table entry
}
impl Readable for GospelContainerImport {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(GospelContainerImport{
            container_name: stream.de()?
        })
    }
}
impl Writeable for GospelContainerImport {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.container_name)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Default)]
pub struct GospelContainer {
    pub(crate) header: GospelContainerHeader,
    pub(crate) imports: Vec<GospelContainerImport>,
    pub(crate) globals: Vec<GospelGlobalDefinition>,
    pub(crate) types: Vec<GospelTypeDefinition>,
    pub(crate) external_types: Vec<GospelExternalTypeReference>,
    pub(crate) static_instances: Vec<GospelStaticTypeInstance>,
    pub(crate) strings: GospelStringTable,
}
impl GospelContainer {
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.strings.get(self.header.container_name)
    }
    /// Reads the type container from the provided data buffer
    pub fn read(data: &[u8]) -> anyhow::Result<GospelContainer> {
        let mut reader = Cursor::new(data);
        Ok(reader.de()?)
    }
}

impl Readable for GospelContainer {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            header: stream.de()?,
            imports: stream.de()?,
            globals: stream.de()?,
            types: stream.de()?,
            external_types: stream.de()?,
            static_instances: stream.de()?,
            strings: stream.de()?,
        })
    }
}
impl Writeable for GospelContainer {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.header)?;
        stream.ser(&self.imports)?;
        stream.ser(&self.globals)?;
        stream.ser(&self.types)?;
        stream.ser(&self.external_types)?;
        stream.ser(&self.static_instances)?;
        stream.ser(&self.strings)?;
        Ok({})
    }
}
