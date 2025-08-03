use crate::gospel_type::{GospelExternalObjectReference, GospelFunctionDefinition, GospelLazyValue, GospelObjectIndexNamePair, GospelStructDefinition, GospelStructNameInfo};
use anyhow::bail;
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub(crate) enum GospelContainerVersion {
    Initial = 0x00, // initial version
}
impl GospelContainerVersion {
    pub(crate) fn current_version() -> GospelContainerVersion {
        GospelContainerVersion::Initial
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub(crate) struct GospelContainerHeader {
    pub(crate) file_magic: u32,
    pub(crate) version: GospelContainerVersion,
    pub(crate) container_name: u32, // name of this container without extension, index to the string table
    pub(crate) is_reference_container: bool, // true if this container only defines public interface and does not contain executable code
}
impl GospelContainerHeader {
    pub(crate) const FILE_MAGIC: u32 = 0x4C505347;
}
impl Default for GospelContainerHeader {
    fn default() -> Self {
        Self{file_magic: Self::FILE_MAGIC, version: GospelContainerVersion::current_version(), container_name: 0, is_reference_container: false}
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub(crate) struct GospelGlobalDefinition {
    pub name: u32, // name of the global, index to the string table
    pub default_value: Option<i32>, // default value of the global, if present
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct GospelStringTable {
    data: Vec<String>,
}
impl GospelStringTable {
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct GospelContainerImport {
    pub(crate) container_name: u32, // name of the imported container, index to the string table entry
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct GospelContainer {
    pub(crate) header: GospelContainerHeader,
    pub(crate) imports: Vec<GospelContainerImport>,
    pub(crate) globals: Vec<GospelGlobalDefinition>,
    pub(crate) functions: Vec<GospelFunctionDefinition>,
    pub(crate) function_names: Vec<GospelObjectIndexNamePair>,
    pub(crate) structs: Vec<GospelStructDefinition>,
    pub(crate) struct_names: Vec<GospelStructNameInfo>,
    pub(crate) external_functions: Vec<GospelExternalObjectReference>,
    pub(crate) external_structs: Vec<GospelExternalObjectReference>,
    pub(crate) lazy_values: Vec<GospelLazyValue>,
    pub(crate) strings: GospelStringTable,
}
impl GospelContainer {
    pub fn container_name(&self) -> anyhow::Result<&str> {
        self.strings.get(self.header.container_name)
    }
    /// Reads the container from the provided data buffer
    pub fn read(data: &[u8]) -> anyhow::Result<Self> {
        Ok(bitcode::deserialize(data)?)
    }
    /// Serializes the container to a data buffer
    pub fn write(&self) -> anyhow::Result<Vec<u8>> {
        Ok(bitcode::serialize(self)?)
    }
}
