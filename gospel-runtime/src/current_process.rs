use std::ptr::{slice_from_raw_parts, slice_from_raw_parts_mut};
use gospel_typelib::type_model::{TargetArchitecture, TargetOperatingSystem};
use crate::memory_access::Memory;

#[derive(Clone)]
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
    fn read_u8(&self, address: u64) -> anyhow::Result<u8> {
        Ok(unsafe { *(address as *const u8) }) }
    fn read_u16(&self, address: u64) -> anyhow::Result<u16> {
        Ok(unsafe { *(address as *const u16) }) }
    fn read_u32(&self, address: u64) -> anyhow::Result<u32> {
        Ok(unsafe { *(address as *const u32) }) }
    fn read_u64(&self, address: u64) -> anyhow::Result<u64> {
        Ok(unsafe { *(address as *const u64) }) }
    fn read_raw_ptr(&self, address: u64) -> anyhow::Result<u64> {
        Ok(unsafe { (*(address as *const *const u8)) as u64 }) }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        let memory_buffer = unsafe { &*slice_from_raw_parts(address as *const u8, buffer.len()) };
        buffer.copy_from_slice(memory_buffer);
        Ok({})
    }
    fn write_u8(&self, address: u64, value: u8) -> anyhow::Result<()> {
        unsafe { *(address as *mut u8) = value; }; Ok({})
    }
    fn write_u16(&self, address: u64, value: u16) -> anyhow::Result<()> {
        unsafe { *(address as *mut u16) = value; }; Ok({})
    }
    fn write_u32(&self, address: u64, value: u32) -> anyhow::Result<()> {
        unsafe { *(address as *mut u32) = value; }; Ok({})
    }
    fn write_u64(&self, address: u64, value: u64) -> anyhow::Result<()> {
        unsafe { *(address as *mut u64) = value; }; Ok({})
    }
    fn write_raw_ptr(&self, address: u64, value: u64) -> anyhow::Result<()> {
        unsafe { *(address as *mut *const u8) = value as *const u8 }; Ok({})
    }
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()> {
        let memory_buffer = unsafe { &mut *slice_from_raw_parts_mut(address as *mut u8, value.len()) };
        memory_buffer.copy_from_slice(value); 
        Ok({})
    }
}
