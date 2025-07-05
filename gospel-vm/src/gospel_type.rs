use std::io::{Read, Write};
use anyhow::anyhow;
use strum_macros::{Display, EnumString, FromRepr};
use crate::bytecode::GospelInstruction;
use crate::ser::{ReadExt, Readable, WriteExt, Writeable};

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr, EnumString)]
#[repr(u8)]
pub enum GospelTargetArch {
    X86_64 = 0x00,
    ARM64 = 0x01,
    ARM64EC = 0x02,
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr, EnumString)]
#[repr(u8)]
pub enum GospelTargetOS {
    None = 0x00,
    Win32 = 0x01,
    Linux = 0x02,
    Darwin = 0x03,
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr, EnumString)]
#[repr(u8)]
pub enum GospelTargetEnv {
    MSVC = 0x00,
    Gnu = 0x01,
    Macho = 0x02,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, Display, EnumString)]
#[repr(u8)]
pub enum GospelValueType {
    Integer = 0x00,
    FunctionPointer = 0x01,
    TypeLayout = 0x02,
}
impl Readable for GospelValueType {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_value_type: u8 = stream.de()?;
        Self::from_repr(raw_value_type).ok_or_else(|| anyhow!("Unknown value type"))
    }
}
impl Writeable for GospelValueType {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(*self as u8))?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, FromRepr, EnumString)]
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
    FunctionIndex = 0x01, // value is a function pointer, data is an ID of the function
    LazyValue = 0x02, // data is an ID of a lazy value, value is returned by evaluation of the value expression
    PlatformConfigProperty = 0x03, // platform config property value, interpret data as GospelPlatformConfigProperty
    GlobalVariableValue = 0x04, // global variable value by name, interpret data as name index
}
impl Readable for GospelStaticValueType {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_value_type: u8 = stream.de()?;
        Self::from_repr(raw_value_type).ok_or_else(|| anyhow!("Unknown static value type"))
    }
}
impl Writeable for GospelStaticValueType {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(*self as u8))?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct GospelStaticValue {
    pub value_type: GospelValueType,
    pub static_type: GospelStaticValueType,
    pub data: u32,
}
impl Readable for GospelStaticValue {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self>  {
        Ok(Self{
            value_type: stream.de()?,
            static_type: stream.de()?,
            data: stream.de()?,
        })
    }
}
impl Writeable for GospelStaticValue {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.value_type)?;
        stream.ser(&(self.static_type as u8))?;
        stream.ser(&self.data)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, FromRepr)]
#[repr(u8)]
pub(crate) enum GospelSlotBinding {
    StaticValue = 0x00, // initialized with static value (if present)
    ArgumentValue = 0x01, // value of the type argument passed to the type definition
}
impl Readable for GospelSlotBinding {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let raw_value_type: u8 = stream.de()?;
        Self::from_repr(raw_value_type).ok_or_else(|| anyhow!("Unknown slot binding"))
    }
}
impl Writeable for GospelSlotBinding {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&(*self as u8))?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelSlotDefinition {
    pub(crate) value_type: GospelValueType,
    pub(crate) binding: GospelSlotBinding,
    pub(crate) static_value: Option<GospelStaticValue>,
    pub(crate) argument_index: u32,
}
impl Readable for GospelSlotDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            value_type: stream.de()?,
            binding: stream.de()?,
            static_value: stream.de()?,
            argument_index: stream.de()?,
        })
    }
}
impl Writeable for GospelSlotDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.value_type)?;
        stream.ser(&self.binding)?;
        stream.ser(&self.static_value)?;
        stream.ser(&self.argument_index)?;
        Ok({})
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GospelFunctionArgument {
    pub argument_type: GospelValueType, // type of the argument
    pub default_value: Option<GospelStaticValue>, // default value for the argument, if available
}
impl Readable for GospelFunctionArgument {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        let argument_type: GospelValueType = stream.de()?;
        let default_value: Option<GospelStaticValue> = stream.de()?;
        Ok(Self{argument_type, default_value})
    }
}
impl Writeable for GospelFunctionArgument {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.argument_type)?;
        stream.ser(&self.default_value)?;
        Ok({})
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GospelFunctionDefinition {
    pub arguments: Vec<GospelFunctionArgument>, // arguments for this function
    pub return_value_type: GospelValueType, // type of the function return value
    pub slots: Vec<GospelSlotDefinition>, // slots to bind to the code
    pub code: Vec<GospelInstruction>, // bytecode for the VM
    pub referenced_strings: Vec<u32>, // indices of strings referenced by the bytecode
}
impl Readable for GospelFunctionDefinition {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            arguments: stream.de()?,
            return_value_type: stream.de()?,
            slots: stream.de()?,
            code: stream.de()?,
            referenced_strings: stream.de()?,
        })
    }
}
impl Writeable for GospelFunctionDefinition {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.arguments)?;
        stream.ser(&self.return_value_type)?;
        stream.ser(&self.slots)?;
        stream.ser(&self.code)?;
        stream.ser(&self.referenced_strings)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub(crate) struct GospelFunctionIndex(u32);
impl GospelFunctionIndex {
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
impl Readable for GospelFunctionIndex {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self(stream.de()?))
    }
}
impl Writeable for GospelFunctionIndex {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.0)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub(crate) struct GospelLazyValue {
    pub function_index: GospelFunctionIndex, // index of the function
    pub arguments: Vec<GospelStaticValue>, // argument values for the function invocation
}
impl Readable for GospelLazyValue {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            function_index: stream.de()?,
            arguments: stream.de()?,
        })
    }
}
impl Writeable for GospelLazyValue {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.function_index)?;
        stream.ser(&self.arguments)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct GospelNamedConstant {
    pub(crate) name: u32, // name of the constant, index to the string table
    pub(crate) value: GospelStaticValue, // value of the constant
}
impl Readable for GospelNamedConstant {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            name: stream.de()?,
            value: stream.de()?,
        })
    }
}
impl Writeable for GospelNamedConstant {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.name)?;
        stream.ser(&self.value)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct GospelFunctionNamePair {
    pub(crate) function_index: u32, // index of a local function
    pub(crate) function_name: u32, // name of the function, index to the string table
}
impl Readable for GospelFunctionNamePair {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            function_index: stream.de()?,
            function_name: stream.de()?,
        })
    }
}
impl Writeable for GospelFunctionNamePair {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.function_index)?;
        stream.ser(&self.function_name)?;
        Ok({})
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub(crate) struct GospelExternalFunctionReference {
    pub import_index: u32, // index of the container from imports from which the named type is imported
    pub function_name: u32, // name of the imported function, index to the string table
}
impl Readable for GospelExternalFunctionReference {
    fn de<S: Read>(stream: &mut S) -> anyhow::Result<Self> {
        Ok(Self{
            import_index: stream.de()?,
            function_name: stream.de()?,
        })
    }
}
impl Writeable for GospelExternalFunctionReference {
    fn ser<S: Write>(&self, stream: &mut S) -> anyhow::Result<()> {
        stream.ser(&self.import_index)?;
        stream.ser(&self.function_name)?;
        Ok({})
    }
}
