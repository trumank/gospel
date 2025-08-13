use serde::{Deserialize, Serialize};
use strum_macros::{Display, EnumString, FromRepr};
use gospel_typelib::type_model::TargetTriplet;
use crate::bytecode::GospelInstruction;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Display, EnumString, FromRepr, Serialize, Deserialize)]
#[repr(u8)]
pub enum GospelValueType {
    Integer,
    Closure,
    TypeReference,
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
impl GospelPlatformConfigProperty {
    /// Resolves a value of the platform config property
    pub fn resolve(self, target: &TargetTriplet) -> i32 {
        match self {
            GospelPlatformConfigProperty::TargetArch => { target.arch as i32 }
            GospelPlatformConfigProperty::TargetOS => { target.sys as i32 }
            GospelPlatformConfigProperty::TargetEnv => { target.env as i32 }
            GospelPlatformConfigProperty::AddressSize => { target.address_size() as i32 }
        }
    }
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
