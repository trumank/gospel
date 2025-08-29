use std::ptr::{slice_from_raw_parts, slice_from_raw_parts_mut};
use gospel_typelib::type_model::{TargetArchitecture, TargetOperatingSystem};
use crate::memory_access::{DataEndianness, Memory};

#[derive(Clone, Default)]
pub struct CurrentProcessMemory {}
impl Memory for CurrentProcessMemory {
    fn target_arch(&self) -> anyhow::Result<Option<TargetArchitecture>> {
        Ok(TargetArchitecture::current_arch())
    }
    fn target_os(&self) -> anyhow::Result<Option<TargetOperatingSystem>> {
        Ok(TargetOperatingSystem::current_os())
    }
    fn address_width(&self) -> anyhow::Result<usize> {
        Ok(size_of::<*const u8>())
    }
    fn data_endianness(&self) -> anyhow::Result<DataEndianness> {
        Ok(DataEndianness::host_endianness())
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        let memory_buffer = unsafe { &*slice_from_raw_parts(address as *const u8, buffer.len()) };
        buffer.copy_from_slice(memory_buffer);
        Ok({})
    }
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()> {
        let memory_buffer = unsafe { &mut *slice_from_raw_parts_mut(address as *mut u8, value.len()) };
        memory_buffer.copy_from_slice(value); 
        Ok({})
    }
}
