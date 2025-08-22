use std::cmp::{Ordering};
use std::hash::{Hash, Hasher};
use std::ops::{Add, Sub};
use std::sync::Arc;
use anyhow::anyhow;
use gospel_typelib::type_model::{TargetArchitecture, TargetOperatingSystem};

/// Interface for reading and writing memory at arbitrary addresses. Address in this context can refer to either relative or absolute address located within this process or another process address space
pub trait Memory {
    /// Returns the target architecture for the backend of this memory
    fn target_arch(&self) -> anyhow::Result<Option<TargetArchitecture>>;
    /// Returns the target architecture for the backend of this memory
    fn target_os(&self) -> anyhow::Result<Option<TargetOperatingSystem>>;
    /// Returns the address width for the memory backend. Address width determines the size of the pointer type
    fn address_width(&self) -> anyhow::Result<usize>;

    /// Allows reading data from this memory backend
    fn read_u8(&self, address: u64) -> anyhow::Result<u8> {
        let mut buffer: [u8; 1] = [0; 1];
        self.read_chunk(address, &mut buffer)?;
        Ok(buffer[0])
    }
    fn read_u16(&self, address: u64) -> anyhow::Result<u16> {
        let mut buffer: [u8; 2] = [0; 2];
        self.read_chunk(address, &mut buffer)?;
        Ok(u16::from_ne_bytes(buffer))
    }
    fn read_u32(&self, address: u64) -> anyhow::Result<u32> {
        let mut buffer: [u8; 4] = [0; 4];
        self.read_chunk(address, &mut buffer)?;
        Ok(u32::from_ne_bytes(buffer))
    }
    fn read_u64(&self, address: u64) -> anyhow::Result<u64> {
        let mut buffer: [u8; 8] = [0; 8];
        self.read_chunk(address, &mut buffer)?;
        Ok(u64::from_ne_bytes(buffer))
    }
    fn read_raw_ptr(&self, address: u64) -> anyhow::Result<u64> {
        match self.address_width()? {
            8 => Ok(self.read_u64(address)?),
            4 => Ok(self.read_u32(address)? as u64),
            _ => Err(anyhow!("Unsupported address width"))
        }
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()>;

    /// Allows writing data to this memory backend. Support for writing data is optional
    fn write_u8(&self, address: u64, value: u8) -> anyhow::Result<()> {
        let buffer: [u8; 1] = [value];
        self.write_chunk(address, &buffer)
    }
    fn write_u16(&self, address: u64, value: u16) -> anyhow::Result<()> {
        let buffer: [u8; 2] = value.to_ne_bytes();
        self.write_chunk(address, &buffer)
    }
    fn write_u32(&self, address: u64, value: u32) -> anyhow::Result<()> {
        let buffer: [u8; 4] = value.to_ne_bytes();
        self.write_chunk(address, &buffer)
    }
    fn write_u64(&self, address: u64, value: u64) -> anyhow::Result<()> {
        let buffer: [u8; 8] = value.to_ne_bytes();
        self.write_chunk(address, &buffer)
    }
    fn write_raw_ptr(&self, address: u64, value: u64) -> anyhow::Result<()> {
        match self.address_width()? {
            8 => self.write_u64(address, value),
            4 => self.write_u32(address, value as u32),
            _ => Err(anyhow!("Unsupported address width"))
        }
    }
    fn write_chunk(&self, address: u64, buffer: &[u8]) -> anyhow::Result<()>;
}

/// Opaque pointer represents a pointer to memory at specific address
#[derive(Clone)]
pub struct OpaquePtr {
    pub memory: Arc<dyn Memory>,
    pub address: u64,
}
impl PartialEq for OpaquePtr {
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address && Arc::ptr_eq(&self.memory, &other.memory)
    }
}
impl Eq for OpaquePtr {}
impl PartialOrd for OpaquePtr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.address.partial_cmp(&other.address)
    }
}
impl Ord for OpaquePtr {
    fn cmp(&self, other: &Self) -> Ordering {
        self.address.cmp(&other.address)
    }
}
impl Hash for OpaquePtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.address.hash(state)
    }
}
impl Add<i64> for OpaquePtr {
    type Output = OpaquePtr;
    fn add(self, rhs: i64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add_signed(rhs).unwrap()}
    }
}
impl Add<u64> for OpaquePtr {
    type Output = OpaquePtr;
    fn add(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add(rhs).unwrap()}
    }
}
impl Add<usize> for OpaquePtr {
    type Output = OpaquePtr;
    fn add(self, rhs: usize) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add(rhs as u64).unwrap()}
    }
}
impl Sub<u64> for OpaquePtr {
    type Output = OpaquePtr;
    fn sub(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub(rhs).unwrap()}
    }
}
impl Sub<usize> for OpaquePtr {
    type Output = OpaquePtr;
    fn sub(self, rhs: usize) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub(rhs as u64).unwrap()}
    }
}
impl OpaquePtr {
    /// Reads data of various sizes from the memory location pointed to by this pointer
    pub fn read_u8(&self) -> anyhow::Result<u8> { self.memory.read_u8(self.address) }
    pub fn read_u16(&self) -> anyhow::Result<u16> { self.memory.read_u16(self.address) }
    pub fn read_u32(&self) -> anyhow::Result<u32> { self.memory.read_u32(self.address) }
    pub fn read_u64(&self) -> anyhow::Result<u64> { self.memory.read_u64(self.address) }
    pub fn read_ptr(&self) -> anyhow::Result<OpaquePtr> { Ok(OpaquePtr{memory: self.memory.clone(), address: self.memory.read_raw_ptr(self.address)?}) }
    pub fn read_chunk(&self, buffer: &mut [u8]) -> anyhow::Result<()> { self.memory.read_chunk(self.address, buffer) }
    /// Writes data of various sizes to the memory location pointed to by this pointer
    pub fn write_u8(&self, value: u8) -> anyhow::Result<()> { self.memory.write_u8(self.address, value) }
    pub fn write_u16(&self, value: u16) -> anyhow::Result<()> { self.memory.write_u16(self.address, value) }
    pub fn write_u32(&self, value: u32) -> anyhow::Result<()> { self.memory.write_u32(self.address, value) }
    pub fn write_u64(&self, value: u64) -> anyhow::Result<()> { self.memory.write_u64(self.address, value) }
    pub fn write_ptr(&self, value: &OpaquePtr) -> anyhow::Result<()> { self.memory.write_raw_ptr(self.address, value.address) }
    pub fn write_chunk(&self, value: &[u8]) -> anyhow::Result<()> { self.memory.write_chunk(self.address, value) }
}
