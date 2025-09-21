use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use gospel_typelib::type_model::TargetTriplet;
use crate::bytecode::GospelInstruction;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, EnumString, Display, Serialize, Deserialize)]
pub enum GospelTargetProperty {
    TargetArch, // target architecture (GospelTargetArch)
    TargetOS, // target operating system (GospelTargetOS)
    TargetEnv, // target environment (GospelTargetEnv)
    AddressSize, // size of the address (a pointer) on the platform, in bytes (8 bytes for 64-bit platforms, 4 bytes for 32-bit platforms)
}
impl GospelTargetProperty {
    /// Resolves a value of the platform config property
    pub fn resolve(self, target: &TargetTriplet) -> u64 {
        match self {
            GospelTargetProperty::TargetArch => { target.arch as u64 }
            GospelTargetProperty::TargetOS => { target.sys as u64 }
            GospelTargetProperty::TargetEnv => { target.env as u64 }
            GospelTargetProperty::AddressSize => { target.address_width() as u64 }
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct GospelFunctionDebugData {
    pub(crate) source_file_name: u32, // index to the string table
    pub(crate) instruction_line_numbers: Vec<i32>, // index is the instruction index, value is the line number. -1 if not known
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct GospelFunctionDefinition {
    pub(crate) name: u32, // name of the function
    pub(crate) exported: bool, // true if function is visible by name outside its container
    pub(crate) num_slots: u32, // number of slots used by the function code
    pub(crate) code: Vec<GospelInstruction>, // bytecode for the VM
    pub(crate) referenced_strings: Vec<u32>, // indices of strings referenced by the bytecode
    pub(crate) referenced_functions: Vec<GospelObjectIndex>, // indices of functions referenced by the bytecode
    pub(crate) debug_data: Option<GospelFunctionDebugData>, // optional debug data for the function
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash, EnumString, Serialize, Deserialize)]
pub(crate) enum GospelObjectIndex {
    Local(u32),
    External(u32),
}

#[derive(Debug, PartialEq, Clone, Hash, Serialize, Deserialize)]
pub(crate) struct GospelExternalObjectReference {
    pub(crate) import_index: u32, // index of the container from imports from which the named type is imported
    pub(crate) object_name: u32, // name of the imported object, index to the string table
}
