use std::str::FromStr;
use anyhow::{anyhow, bail};
use serde::{Deserialize, Serialize};
use strum_macros::EnumString;

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetArchitecture {
    X86_64,
    ARM64,
    ARM64EC,
}
impl TargetArchitecture {
    /// Returns the architecture current binary has been compiled for (if it can be represented)
    pub fn current_arch() -> Option<TargetArchitecture> {
        match std::env::consts::ARCH {
            "x86_64" => Some(TargetArchitecture::X86_64),
            "aarch64" => Some(TargetArchitecture::ARM64),
            _ => None,
        }
    }
}

/// Corresponds to <sys> in LLVM target triplet
/// Target system generally defines calling convention used and object file format
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetOperatingSystem {
    None,
    Win32,
    Linux,
    Darwin,
}
impl TargetOperatingSystem {
    /// Returns the OS the binary has been compiled for (if it can be represented)
    pub fn current_os() -> Option<TargetOperatingSystem> {
        match std::env::consts::OS {
            "windows" => Some(TargetOperatingSystem::Win32),
            "linux" => Some(TargetOperatingSystem::Linux),
            "android" => Some(TargetOperatingSystem::Linux),
            "macos" => Some(TargetOperatingSystem::Darwin),
            "ios" => Some(TargetOperatingSystem::Darwin),
            _ => None,
        }
    }
    /// Returns the default environment for the OS in question. Returns none for bare metal
    pub fn default_env(self) -> Option<TargetEnvironment> {
        match self {
            TargetOperatingSystem::None => None,
            TargetOperatingSystem::Win32 => Some(TargetEnvironment::MSVC),
            TargetOperatingSystem::Linux => Some(TargetEnvironment::Gnu),
            TargetOperatingSystem::Darwin => Some(TargetEnvironment::Macho),
        }
    }
}

/// Corresponds to <env> in LLVM target triplet
/// Target env determines the ABI rules used for type layout calculation, for example semantics used for C++ class inheritance and exception handling
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetEnvironment {
    MSVC,
    Gnu,
    Macho,
}

/// Target triplet defines the target which the type layouts are being calculated for
/// This includes the operating system, the processor architecture, and environment (ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct TargetTriplet {
    pub arch: TargetArchitecture,
    pub sys: TargetOperatingSystem,
    pub env: TargetEnvironment,
}
impl TargetTriplet {
    /// Returns the address size for the provided target triplet
    pub fn address_size(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    fn uses_aligned_base_class_size(&self) -> bool {
        self.env == TargetEnvironment::MSVC // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
    /// Returns the target that the current executable has been compiled for
    pub fn current_target() -> Option<TargetTriplet> {
        let current_arch = TargetArchitecture::current_arch();
        let current_os = TargetOperatingSystem::current_os();
        let default_env = current_os.as_ref().and_then(|x| x.default_env());

        if current_arch.is_none() || current_os.is_none() || default_env.is_none() {
            None
        } else { Some(TargetTriplet {
            arch: current_arch.unwrap(),
            sys: current_os.unwrap(),
            env: default_env.unwrap(),
        }) }
    }
    pub fn parse(triplet_str: &str) -> anyhow::Result<TargetTriplet> {
        let splits: Vec<&str> = triplet_str.split('-').collect();
        if splits.len() <= 2 {
            bail!("Target triplet string too short, need at least 2 parts (<arch>-<os>)");
        }
        if splits.len() > 3 {
            bail!("Target triplet string too long, should consist of at most 3 parts (<arch>-<os>-<env>)");
        }
        let arch = TargetArchitecture::from_str(splits[0])
            .map_err(|x| anyhow!("Failed to parse arch: {}", x.to_string()))?;
        let sys = TargetOperatingSystem::from_str(splits[1])
            .map_err(|x| anyhow!("Failed to parse OS: {}", x.to_string()))?;
        let env = if splits.len() >= 3 {
            TargetEnvironment::from_str(splits[2])
                .map_err(|x| anyhow!("Failed to parse env: {}", x.to_string()))?
        } else {
            sys.default_env().ok_or_else(|| anyhow!("Default env for OS not available please specify env manually (<arch>-<os>-<env>)"))?
        };
        Ok(TargetTriplet {arch, sys, env})
    }
}

/// Represents a primitive type with a target-dependent or fixed size
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimitiveTypeKind {
    Void,
    Char,
    UnsignedChar,
    WideChar,
    Int,
    UnsignedInt,
    Float,
    Double,
    Bool,
    Long,
    UnsignedLong,
    Char8,
    Char16,
    Char32,
}

/// Represents a primitive type with a resolved size
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveType {
    /// Kind of this primitive
    pub kind: PrimitiveTypeKind,
    /// Alignment of this primitive, in bytes
    pub alignment: usize,
    /// Size of this primitive, in bytes
    pub size: usize,
}

/// Represents a statically sized array type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArrayType {
    /// Index of the element type for this array
    pub element_type_index: usize,
    /// Length of this array type
    pub array_size: usize,
}

/// Represents an intrinsic pointer type with a known pointee type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PointerType {
    /// Index of the pointee type for this pointer
    pub pointee_type_index: usize,
}

/// Represents a base class for a class
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BaseClass {
    /// Offset of the start of this base class data from the start of the class
    pub offset: usize,
    /// Size in bytes of the parent class field within this class. This can be an aligned or unaligned type size depending on the ABI
    pub size: usize,
    /// Index of the base class type
    pub type_index: usize,
}

/// Represents a location of the bitfield within the field data type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitfieldLocation {
    bitfield_bit_offset: usize,
    bitfield_bit_width: usize,
}

/// Represents a layout of a single field in a type layout
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UserDefinedTypeField {
    pub name: String,
    /// Offset of the field from the base of the class
    pub offset: usize,
    /// Index of the type for this field
    pub type_index: usize,
    /// If this field is a bitfield, this is the location information for it
    pub bitfield_location: Option<BitfieldLocation>,
}

/// Represents a user defined struct, class or union type, with optional base classes and fields defined in it
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct UserDefinedType {
    pub name: String,
    /// Minimum alignment requirement of this type in bytes
    pub alignment: usize,
    /// Total size of the type base classes and fields without the padding to the alignment
    pub unaligned_size: usize,
    /// Total size of the type, padded to the multiple of the alignment
    pub size: usize,
    /// All base classes for this type
    pub base_classes: Vec<BaseClass>,
    /// All fields defined in this type. Does not include fields defined in the base classes
    pub fields: Vec<UserDefinedTypeField>,
}

/// Represents a single type with references to other types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Type {
    Primitive(PrimitiveType),
    Array(ArrayType),
    Pointer(PointerType),
    UDT(UserDefinedType),
}

/// Represents an isolated type graph
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeGraph {
    /// The target triplet for which this type graph has been created
    pub target: TargetTriplet,
    /// All types referenced by the root type and the root type itself
    pub types: Vec<Type>,
    /// Index of the root type this root graph represents
    pub root_type_index: usize,
}
