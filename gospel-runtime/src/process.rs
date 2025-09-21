use process_memory::{CopyAddress, ProcessHandle, PutAddress};
use gospel_typelib::type_model::TargetTriplet;
use crate::external_memory::{Memory};

pub struct LocalProcessMemory {
    target_triplet: TargetTriplet,
    process_handle: ProcessHandle,
}
impl Memory for LocalProcessMemory {
    fn target_triplet(&self) -> TargetTriplet {
        self.target_triplet
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.copy_address(address as usize, buffer)?)
    }
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()> {
        Ok(self.process_handle.put_address(address as usize, value)?)
    }
}
