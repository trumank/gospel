use std::ptr::{slice_from_raw_parts, slice_from_raw_parts_mut};
use gospel_typelib::type_model::TargetTriplet;
use crate::external_memory::{Memory};

#[derive(Clone, Default)]
pub struct CurrentProcessMemory {}
impl Memory for CurrentProcessMemory {
    fn target_triplet(&self) -> TargetTriplet {
        TargetTriplet::current_target().unwrap()
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
