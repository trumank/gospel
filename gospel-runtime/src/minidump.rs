use anyhow::{anyhow, bail};
use minidump::{Endian, MinidumpSystemInfo, UnifiedMemory, UnifiedMemoryList};
use minidump::system_info::{Cpu, Os, PointerWidth};
use gospel_typelib::type_model::{TargetArchitecture, TargetOperatingSystem};
use crate::memory_access::{DataEndianness, Memory};

pub trait MinidumpAccess {
    /// Retrieves the system info for the minidump
    fn minidump_system_info(&self) -> MinidumpSystemInfo;
    /// Allows access to the minidump memory list within the scope of the lambda
    fn use_minidump_memory_list<T, S: FnOnce(&UnifiedMemoryList) -> T>(&self, op: S) -> T;
}

pub struct MinidumpMemory<T : MinidumpAccess> {
    minidump: T,
}
impl<T : MinidumpAccess> Memory for MinidumpMemory<T> {
    fn target_arch(&self) -> anyhow::Result<Option<TargetArchitecture>> {
        match self.minidump.minidump_system_info().cpu {
            Cpu::Arm64 => Ok(Some(TargetArchitecture::ARM64)),
            Cpu::X86_64 => Ok(Some(TargetArchitecture::X86_64)),
            _ => Ok(None),
        }
    }
    fn target_os(&self) -> anyhow::Result<Option<TargetOperatingSystem>> {
        match self.minidump.minidump_system_info().os {
            Os::Windows => Ok(Some(TargetOperatingSystem::Win32)),
            Os::Linux => Ok(Some(TargetOperatingSystem::Linux)),
            Os::Android => Ok(Some(TargetOperatingSystem::Linux)),
            Os::MacOs => Ok(Some(TargetOperatingSystem::Darwin)),
            Os::Ios => Ok(Some(TargetOperatingSystem::Darwin)),
            _ => Ok(None),
        }
    }
    fn address_width(&self) -> anyhow::Result<usize> {
        match self.minidump.minidump_system_info().cpu.pointer_width() {
            PointerWidth::Bits64 => Ok(8),
            PointerWidth::Bits32 => Ok(4),
            _ => Err(anyhow!("Unknown pointer width for minidump")),
        }
    }
    fn data_endianness(&self) -> anyhow::Result<DataEndianness> {
        self.minidump.use_minidump_memory_list(|x| {
            let first_memory = x.iter().next().ok_or_else(|| anyhow!("Minidump does not contain any memory slices"))?;
            let minidump_endian = match first_memory {
                UnifiedMemory::Memory(x) => x.endian,
                UnifiedMemory::Memory64(x) => x.endian,
            };
            match minidump_endian {
                Endian::Big => Ok(DataEndianness::BigEndian),
                Endian::Little => Ok(DataEndianness::LittleEndian),
            }
        })
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
