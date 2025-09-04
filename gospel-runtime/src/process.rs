use process_memory::{Architecture, CopyAddress, ProcessHandle, PutAddress};
use crate::memory_access::{DataEndianness, Memory};

pub struct LocalProcessMemory {
    process_handle: ProcessHandle,
}
impl Memory for LocalProcessMemory {
    fn address_width(&self) -> usize {
        match self.process_handle.get_pointer_width() {
            Architecture::Arch64Bit => 8,
            Architecture::Arch32Bit => 4,
            _ => panic!("Unsupported process pointer width"),
        }
    }
    fn data_endianness(&self) -> DataEndianness {
        DataEndianness::host_endianness()
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.copy_address(address as usize, buffer)?)
    }
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.put_address(address as usize, value)?)
    }
}
