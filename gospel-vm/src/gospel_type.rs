use serde::{Deserialize, Serialize};
use strum_macros::{Display, EnumString, FromRepr};
use crate::bytecode::GospelInstruction;

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString)]
#[repr(u8)]
pub enum GospelTargetArch {
    X86_64,
    ARM64,
    ARM64EC,
}
impl GospelTargetArch {
    /// Returns the architecture current binary has been compiled for (if it can be represented)
    pub fn current_arch() -> Option<GospelTargetArch> {
        match std::env::consts::ARCH {
            "x86_64" => Some(GospelTargetArch::X86_64),
            "aarch64" => Some(GospelTargetArch::ARM64),
            _ => None,
        }
    }
}

/// Corresponds to <sys> in LLVM target triplet
/// Target system generally defines calling convention used and object file format
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum GospelTargetOS {
    None,
    Win32,
    Linux,
    Darwin,
}
impl GospelTargetOS {
    /// Returns the OS the binary has been compiled for (if it can be represented)
    pub fn current_os() -> Option<GospelTargetOS> {
        match std::env::consts::OS {
            "windows" => Some(GospelTargetOS::Win32),
            "linux" => Some(GospelTargetOS::Linux),
            "android" => Some(GospelTargetOS::Linux),
            "macos" => Some(GospelTargetOS::Darwin),
            "ios" => Some(GospelTargetOS::Darwin),
            _ => None,
        }
    }
    /// Returns the default environment for the OS in question. Returns none for bare metal
    pub fn default_env(self) -> Option<GospelTargetEnv> {
        match self {
            GospelTargetOS::None => None,
            GospelTargetOS::Win32 => Some(GospelTargetEnv::MSVC),
            GospelTargetOS::Linux => Some(GospelTargetEnv::Gnu),
            GospelTargetOS::Darwin => Some(GospelTargetEnv::Macho),
        }
    }
}

/// Corresponds to <env> in LLVM target triplet
/// Target env determines the ABI rules used for type layout calculation, for example semantics used for C++ class inheritance and exception handling
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum GospelTargetEnv {
    MSVC,
    Gnu,
    Macho,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Display, EnumString, FromRepr, Serialize, Deserialize)]
#[repr(u8)]
pub enum GospelValueType {
    Integer,
    Closure,
    TypeLayout,
    Array,
    Struct,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, EnumString, Serialize, Deserialize)]
pub enum GospelPlatformConfigProperty {
    TargetArch, // target architecture (GospelTargetArch)
    TargetOS, // target operating system (GospelTargetOS)
    TargetEnv, // target environment (GospelTargetEnv)
    AddressSize, // size of the address (a pointer) on the platform, in bytes (8 bytes for 64-bit platforms, 4 bytes for 32-bit platforms)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Serialize, Deserialize)]
pub(crate) enum GospelStaticValue {
    Integer(i32),
    FunctionIndex(GospelObjectIndex), // value is a closure with no arguments captured, data is an ID of the function to create a closure from
    PlatformConfigProperty(GospelPlatformConfigProperty), // platform config property value, interpret data as GospelPlatformConfigProperty
    GlobalVariableValue(u32), // global variable value by name, interpret data as name index
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub(crate) enum GospelSlotBinding {
    Uninitialized,
    StaticValue(GospelStaticValue),
    ArgumentValue(u32),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub(crate) struct GospelSlotDefinition {
    pub(crate) value_type: GospelValueType,
    pub(crate) binding: GospelSlotBinding,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub(crate) struct GospelFunctionArgument {
    pub(crate) argument_type: GospelValueType, // type of the argument
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
    pub(crate) arguments: Vec<GospelFunctionArgument>, // arguments for this function
    pub(crate) return_value_type: GospelValueType, // type of the function return value
    pub(crate) slots: Vec<GospelSlotDefinition>, // slots to bind to the code
    pub(crate) code: Vec<GospelInstruction>, // bytecode for the VM
    pub(crate) referenced_strings: Vec<u32>, // indices of strings referenced by the bytecode
    pub(crate) referenced_structs: Vec<GospelObjectIndex>, // indices of structures referenced by the bytecode
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

#[derive(Debug, PartialEq, Clone, Hash, Serialize, Deserialize)]
pub(crate) struct GospelStructFieldDefinition {
    pub(crate) field_type: GospelValueType,
    pub(crate) field_name: u32,
}

#[derive(Debug, PartialEq, Clone, Hash, Serialize, Deserialize)]
pub(crate) struct GospelStructDefinition {
    pub(crate) name: u32, // name of the struct, index in the string table
    pub(crate) exported: bool, // true if struct is visible by name outside its container
    pub(crate) fields: Vec<GospelStructFieldDefinition>, // fields of the struct
}
