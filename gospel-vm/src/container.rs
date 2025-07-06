use std::io::{Cursor, Read, Write};
use anyhow::{anyhow, bail};
use strum_macros::{Display, FromRepr};
use crate::gospel_type::{GospelExternalFunctionReference, GospelFunctionDeclaration, GospelFunctionDefinition, GospelFunctionNamePair, GospelGlobalDeclaration, GospelLazyValue};
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, FromRepr, Display)]
#[repr(u32)]
pub enum GospelCommonFileType {
    Container = 0x0,
    RefContainer = 0x1,
}
impl Readable for GospelCommonFileType {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        GospelCommonFileType::from_repr(stream.de()?).ok_or_else(|| anyhow!("Unknown common file type"))
    }
}
impl Writeable for GospelCommonFileType {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(*self as u32))
    }
}

#[derive(Debug, Clone)]
pub struct GospelCommonFileHeader {
    pub file_magic: u32,
    pub header_version: u32,
    pub file_type: GospelCommonFileType,
}
impl Readable for GospelCommonFileHeader {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let file_magic: u32 = stream.de()?;
        if file_magic != Self::FILE_MAGIC {
            bail!("Invalid file magic: expected {:x}, got {:x}", GospelCommonFileHeader::FILE_MAGIC, file_magic);
        }
        let header_version: u32 = stream.de()?;
        if header_version != Self::HEADER_VERSION_INITIAL {
            bail!("Incompatible header version, expected {}, got {}", Self::HEADER_VERSION_INITIAL, header_version);
        }
        let file_type: GospelCommonFileType = stream.de()?;
        Ok(Self{file_magic, header_version, file_type})
    }
}
impl Writeable for GospelCommonFileHeader {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.file_magic)?;
        stream.ser(&self.header_version)?;
        stream.ser(&self.file_type)?;
        Ok({})
    }
}
impl GospelCommonFileHeader {
    pub const FILE_MAGIC: u32 = 0x4C505347;
    pub const HEADER_VERSION_INITIAL: u32 = 1;

    fn create(file_type: GospelCommonFileType) -> GospelCommonFileHeader {
        GospelCommonFileHeader{
            file_magic: Self::FILE_MAGIC,
            header_version: Self::HEADER_VERSION_INITIAL,
            file_type,
        }
    }
    fn expect_file_type(&self, file_type: GospelCommonFileType) -> anyhow::Result<()> {
        if self.file_type != file_type {
            bail!("This file is a {}. Attempt to read contents as {}", self.file_type, file_type);
        }
        Ok({})
    }

    /// Attempts to read the file header as gospel file header
    pub fn try_read_file_header(data: &[u8]) -> anyhow::Result<GospelCommonFileHeader> {
        let mut reader = Cursor::new(data);
        Ok(reader.de()?)
    }
}


#[derive(Debug, Clone, Default)]
pub struct GospelContainer {
    pub(crate) header: GospelContainerHeader,
    pub(crate) imports: Vec<GospelContainerImport>,
    pub(crate) globals: Vec<GospelGlobalDefinition>,
    pub(crate) functions: Vec<GospelFunctionDefinition>,
    pub(crate) function_names: Vec<GospelFunctionNamePair>,
    pub(crate) external_functions: Vec<GospelExternalFunctionReference>,
    pub(crate) lazy_values: Vec<GospelLazyValue>,
    pub(crate) strings: GospelStringTable,
}
impl GospelContainer {
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.strings.get(self.header.container_name)
    }
    /// Reads the container from the provided data buffer
    pub fn read(data: &[u8]) -> anyhow::Result<Self> {
        let mut reader = Cursor::new(data);
        let common_header: GospelCommonFileHeader = reader.de()?;
        common_header.expect_file_type(GospelCommonFileType::Container)?;
        Ok(reader.de()?)
    }
    /// Serializes the container to a data buffer
    pub fn write(&self) -> anyhow::Result<Vec<u8>> {
        let mut data: Vec<u8> = Vec::new();
        let mut writer = Cursor::new(&mut data);
        let common_header = GospelCommonFileHeader::create(GospelCommonFileType::Container);
        writer.ser(&common_header)?;
        writer.ser(self)?;
        Ok(data)
    }
}

impl Readable for GospelContainer {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            header: stream.de()?,
            imports: stream.de()?,
            globals: stream.de()?,
            functions: stream.de()?,
            function_names: stream.de()?,
            external_functions: stream.de()?,
            lazy_values: stream.de()?,
            strings: stream.de()?,
        })
    }
}
impl Writeable for GospelContainer {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.header)?;
        stream.ser(&self.imports)?;
        stream.ser(&self.globals)?;
        stream.ser(&self.functions)?;
        stream.ser(&self.function_names)?;
        stream.ser(&self.external_functions)?;
        stream.ser(&self.lazy_values)?;
        stream.ser(&self.strings)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Default)]
pub struct GospelRefContainer {
    pub(crate) header: GospelContainerHeader,
    pub(crate) globals: Vec<GospelGlobalDeclaration>,
    pub(crate) functions: Vec<GospelFunctionDeclaration>,
    pub(crate) strings: GospelStringTable,
}
impl GospelRefContainer {
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.strings.get(self.header.container_name)
    }
    /// Reads the reference container from the provided data buffer
    pub fn read(data: &[u8]) -> anyhow::Result<Self> {
        let mut reader = Cursor::new(data);
        let common_header: GospelCommonFileHeader = reader.de()?;
        common_header.expect_file_type(GospelCommonFileType::RefContainer)?;
        Ok(reader.de()?)
    }
    /// Serializes the reference container to a data buffer
    pub fn write(&self) -> anyhow::Result<Vec<u8>> {
        let mut data: Vec<u8> = Vec::new();
        let mut writer = Cursor::new(&mut data);
        let common_header = GospelCommonFileHeader::create(GospelCommonFileType::RefContainer);
        writer.ser(&common_header)?;
        writer.ser(self)?;
        Ok(data)
    }
}

impl Readable for GospelRefContainer {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            header: stream.de()?,
            globals: stream.de()?,
            functions: stream.de()?,
            strings: stream.de()?,
        })
    }
}
impl Writeable for GospelRefContainer {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.header)?;
        stream.ser(&self.globals)?;
        stream.ser(&self.functions)?;
        stream.ser(&self.strings)?;
        Ok({})
    }
}
