use anyhow::anyhow;
use process_memory::{Architecture, CopyAddress, ProcessHandle, PutAddress};
use gospel_typelib::type_model::{TargetArchitecture, TargetOperatingSystem};
use crate::memory_access::Memory;

pub struct LocalProcessMemory {
    process_handle: ProcessHandle,
}
impl Memory for LocalProcessMemory {
    fn target_arch(&self) -> anyhow::Result<Option<TargetArchitecture>> {
        // This is not accurate in case the process is emulated (like with Windows or Mac on ARM64 being able to emulate X64), but this is the best guess
        Ok(TargetArchitecture::current_arch())
    }
    fn target_os(&self) -> anyhow::Result<Option<TargetOperatingSystem>> {
        // This is not accurate in case the process is emulated (e.g. running under Wine on Linux), but this is the best guess
        Ok(TargetOperatingSystem::current_os())
    }
    fn address_width(&self) -> anyhow::Result<usize> {
        match self.process_handle.get_pointer_width() {
            Architecture::Arch64Bit => Ok(8),
            Architecture::Arch32Bit => Ok(4),
            _ => Err(anyhow!("Unsupported process pointer width")),
        }
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.copy_address(address as usize, buffer)?)
    }
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.put_address(address as usize, value)?)
    }
}
