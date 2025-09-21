use crate::external_memory::Memory;
use anyhow::{anyhow, bail};
use minidump::system_info::{Cpu, Os};
use minidump::{MinidumpSystemInfo, UnifiedMemoryList};
use gospel_typelib::target_triplet::{TargetArchitecture, TargetEnvironment, TargetOperatingSystem, TargetTriplet};

pub trait MinidumpAccess {
    /// Retrieves the system info for the minidump
    fn minidump_system_info(&self) -> MinidumpSystemInfo;
    /// Allows access to the minidump memory list within the scope of the lambda
    fn use_minidump_memory_list<T, S: FnOnce(&UnifiedMemoryList) -> T>(&self, op: S) -> T;
}
fn default_target_triplet_for_minidump<T: MinidumpAccess>(minidump: &T) -> TargetTriplet {
    let target_arch = match minidump.minidump_system_info().cpu {
        Cpu::Arm64 => TargetArchitecture::ARM64,
        Cpu::X86_64 => TargetArchitecture::X86_64,
        _ => panic!("Unsupported dump Arch")
    };
    let (target_os, target_env) = match minidump.minidump_system_info().os {
        Os::Windows => (TargetOperatingSystem::Win32, None),
        Os::Linux => (TargetOperatingSystem::Linux, None),
        Os::MacOs => (TargetOperatingSystem::Darwin, None),
        Os::Ios => (TargetOperatingSystem::Darwin, None),
        Os::Android => (TargetOperatingSystem::Linux, Some(TargetEnvironment::Android)),
        _ => panic!("Unsupported dump OS")
    };
    TargetTriplet{arch: target_arch, sys: target_os, env: target_env}
}

pub struct MinidumpMemory<T : MinidumpAccess> {
    target_triplet: TargetTriplet,
    minidump: T,
}
impl<T : MinidumpAccess> MinidumpMemory<T> {
    pub fn create(minidump: T, target_triplet_override: Option<TargetTriplet>) -> Self {
        let target_triplet = target_triplet_override.unwrap_or_else(|| default_target_triplet_for_minidump(&minidump));
        Self{minidump, target_triplet}
    }
}
impl<T : MinidumpAccess> Memory for MinidumpMemory<T> {
    fn target_triplet(&self) -> TargetTriplet {
        self.target_triplet
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        self.minidump.use_minidump_memory_list(|memory_list| {
            let memory = memory_list.memory_at_address(address).ok_or_else(|| anyhow!("Memory at address {} is not included in the minidump", address))?;
            let memory_start_offset = address - memory.base_address();
            let memory_end_offset = memory_start_offset + buffer.len() as u64;
            if memory_end_offset > memory.size() {
                bail!("Could not read {} bytes of memory from minidump at address {} (only {} bytes available)", buffer.len(), address, memory.size() - memory_start_offset);
            }
            let data_slice: &[u8] = &memory.bytes()[memory_start_offset as usize..memory_end_offset as usize];
            buffer.copy_from_slice(data_slice);
            Ok({})
        })
    }
    fn write_chunk(&self, _address: u64, _value: &[u8]) -> anyhow::Result<()> {
        bail!("Minidumps are read-only and cannot be modified")
    }
}
