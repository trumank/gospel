use std::collections::HashSet;
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use lazy_static::lazy_static;

/// Represents possible bit width values for integral types
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Display, EnumString)]
pub enum BitWidth {
    Width8,
    Width16,
    Width32,
    Width64,
}
impl BitWidth {
    /// Returns bit width value in bytes
    pub fn value_in_bytes(self) -> usize {
        match self {
            BitWidth::Width8 => 1,
            BitWidth::Width16 => 2,
            BitWidth::Width32 => 4,
            BitWidth::Width64 => 8,
        }
    }
}

/// Describes possible endianness of the data
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DataEndianness {
    LittleEndian,
    BigEndian,
}

/// Represents a target triplet with unparsed textual components that have been disambiguated
#[derive(Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct RawTargetTriplet<'a> {
    pub arch_and_sub: &'a str,
    pub vendor: &'a str,
    pub sys: &'a str,
    pub abi: Option<&'a str>,
}

/// Parses given target triplet string into the disambiguated raw target triplet
pub fn parse_raw_target_triplet(target_triplet_str: &str) -> RawTargetTriplet<'_> {
    // String format: <arch><sub>-<vendor>-<sys>-<abi>. Sub, vendor and abi are optional
    let components: Vec<&str> = target_triplet_str.split("-").collect();
    if components.len() < 2 || components.len() > 4 {
        panic!("Invalid TARGET format '{}'. Expected from 2 to 4 components", target_triplet_str);
    }
    if components.len() == 2 {
        // For 2 components, the format is not ambiguous and is <arch><sub>-<sys>. Default ABI is assumed in this case, as well as "unknown" vendor
        RawTargetTriplet{arch_and_sub: components[0], vendor: "unknown", sys: components[1], abi: None}
    } else if components.len() == 4 {
        // For 4 components, the format is not ambiguous and is <arch><sub>-<vendor>-<sys>-<abi> with all components present
        RawTargetTriplet{arch_and_sub: components[0], vendor: components[1], sys: components[2], abi: Some(components[3])}
    } else if components.len() == 3 {
        // For 3 components, the format is ambiguous. It could be either <arch><sub>-<sys>-<abi> or <arch><sub>-<vendor>-<sys>
        // We can disambiguate by checking against known vendors and systems, and then fall back to <arch><sub>-<sys>
        lazy_static! {
            static ref known_vendors: HashSet<&'static str> = HashSet::from(["esp32", "esp32s2", "apple", "win7", "uwp", "unknown", "pc", "lynx", "unikraft", "nvidia", "wrs", "sny", "mti", "amd", "nintendo"]);
            static ref known_oss: HashSet<&'static str> = HashSet::from(["none", "windows", "darwin", "freebsd", "fuchsia", "haiku", "hermit", "hurd-gnu", "illumos", "l4re", "linux", "dragonfly", "solaris", "nto", "cygwin", "lynx", "s178", "netbsd", "switch", "watchos", "visionos", "tvos", "ios"]);
        }
        // If second component is a well-known vendor name or third component is well-known OS name, this is <arch><sub>-<vendor>-<sys>
        if known_vendors.contains(components[1]) || known_oss.contains(components[2]) {
            RawTargetTriplet{arch_and_sub: components[0], vendor: components[1], sys: components[2], abi: None}
        } else if known_vendors.contains(components[1]) {
            // If second component is a well-known OS name, this is <arch><sub>-<sys>-<abi>
            RawTargetTriplet{arch_and_sub: components[0], vendor: "unknown", sys: components[1], abi: Some(components[2])}
        } else {
            // Otherwise, assume second component is vendor name, and third component is an OS name
            RawTargetTriplet{arch_and_sub: components[0], vendor: components[1], sys: components[2], abi: None}
        }
    } else {
        panic!("Invalid size for target triplet: {}", components.len());
    }
}

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
#[repr(u8)]
pub enum TargetArchitecture {
    X86_64,
    ARM64,
    ARM64EC,
}

/// Corresponds to <sys> in LLVM target triplet
/// Target system generally defines calling convention used and object file format
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
#[repr(u8)]
pub enum TargetOperatingSystem {
    None,
    Win32,
    Linux,
    Darwin,
}

/// Corresponds to <env> in LLVM target triplet
/// Target env determines the ABI rules used for type layout calculation, for example semantics used for C++ class inheritance and exception handling
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
#[repr(u8)]
pub enum TargetEnvironment {
    MSVC,
    Gnu,
    Android,
}

/// Target triplet defines the target which the type layouts are being calculated for
/// This includes the operating system, the processor architecture, and environment (ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub struct TargetTriplet {
    pub arch: TargetArchitecture,
    pub sys: TargetOperatingSystem,
    pub env: Option<TargetEnvironment>,
}
impl TargetTriplet {
    pub fn is_windows_msvc_target(&self) -> bool {
        self.sys == TargetOperatingSystem::Win32 && (self.env == None || self.env == Some(TargetEnvironment::MSVC))
    }

    /// Returns the address width for the provided target triplet
    pub fn address_width(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    /// Returns the data endianness for the provided target triplet
    pub fn data_endianness(&self) -> DataEndianness {
        DataEndianness::LittleEndian // All currently supported architectures are Little Endian
    }
    /// Returns the size of the "long" type for the provided target triplet
    pub fn long_size(&self) -> BitWidth {
        // 4 on Win32, 8 on everything else
        if self.sys == TargetOperatingSystem::Win32 { BitWidth::Width32 } else { BitWidth::Width64 }
    }
    /// Returns the size of the "wchar_t" type for the provided target triplet
    pub fn wide_char_size(&self) -> BitWidth {
        // 2 on Win32, 4 on everything else
        if self.sys == TargetOperatingSystem::Win32 { BitWidth::Width16 } else { BitWidth::Width32 }
    }
    pub fn uses_aligned_base_class_size(&self) -> bool {
        self.is_windows_msvc_target() // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
    pub fn parse_from_raw(raw_target_triplet: RawTargetTriplet) -> Option<TargetTriplet> {
        let arch = match raw_target_triplet.arch_and_sub {
            "x86_64" => TargetArchitecture::X86_64,
            "aarch64" => TargetArchitecture::ARM64,
            "arm64ec" => TargetArchitecture::ARM64EC,
            _ => { return None; }
        };
        let sys = match raw_target_triplet.sys {
            "windows" => TargetOperatingSystem::Win32,
            "linux" => TargetOperatingSystem::Linux,
            "darwin" => TargetOperatingSystem::Darwin,
            "none" => TargetOperatingSystem::None,
            _ => { return None ; }
        };
        let env = match raw_target_triplet.abi {
            Some("msvc") => Some(TargetEnvironment::MSVC),
            Some("gnu") => Some(TargetEnvironment::Gnu),
            Some("android") => Some(TargetEnvironment::Android),
            None => None,
            _ => { return None; }
        };
        Some(TargetTriplet{arch, sys, env})
    }
    /// Parses the given string into a target triplet
    pub fn parse(triplet_str: &str) -> Option<TargetTriplet> {
        let raw_target_triplet = parse_raw_target_triplet(triplet_str);
        Self::parse_from_raw(raw_target_triplet)
    }
}
