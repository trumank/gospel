use std::cmp::{Ordering};
use std::hash::{Hash, Hasher};
use std::ops::{Add, Deref, DerefMut, Sub};
use std::ptr::{slice_from_raw_parts, slice_from_raw_parts_mut};
use std::sync::Arc;
use paste::paste;

/// Describes possible endianness of the data
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DataEndianness {
    LittleEndian,
    BigEndian,
}
macro_rules! impl_endian_aware_type {
    ($data_type: ident) => {
        paste! {
            pub fn [<$data_type _from_bytes>](self, bytes: [u8; size_of::<$data_type>()]) -> $data_type {
                match self {
                    DataEndianness::LittleEndian => $data_type::from_le_bytes(bytes),
                    DataEndianness::BigEndian => $data_type::from_be_bytes(bytes),
                }
            }
            pub fn [<$data_type _to_bytes>](self, value: $data_type) -> [u8; size_of::<$data_type>()] {
                match self {
                    DataEndianness::LittleEndian => value.to_le_bytes(),
                    DataEndianness::BigEndian => value.to_be_bytes(),
                }
            }
            pub fn [<$data_type _array_from_bytes>](self, bytes: &[u8], data: &mut [$data_type]) {
                assert_eq!(bytes.len(), data.len() * size_of::<$data_type>());
                if DataEndianness::host_endianness() == self {
                    // If endianness is the same between the host and the target, we can just transmute bytes
                    data.copy_from_slice(unsafe { &*slice_from_raw_parts(bytes.as_ptr() as *const $data_type, data.len()) })
                } else {
                    // Endianness flip is necessary
                    for data_index in 0..data.len() {
                        let start_index = data_index * size_of::<$data_type>();
                        let bytes_slice = &bytes[start_index..(start_index + size_of::<$data_type>())];
                        let mut conversion_buffer: [u8; size_of::<$data_type>()] = [0; size_of::<$data_type>()];
                        conversion_buffer.copy_from_slice(bytes_slice);
                        data[data_index] = self.[<$data_type _from_bytes>](conversion_buffer)
                    }
                }
            }
            pub fn [<$data_type _array_to_bytes>](self, data: &[$data_type], bytes: &mut [u8]) {
                assert_eq!(bytes.len(), data.len() * size_of::<$data_type>());
                if DataEndianness::host_endianness() == self {
                    // If endianness is the same between the host and the target, we can just transmute bytes
                    bytes.copy_from_slice(unsafe { &*slice_from_raw_parts(data.as_ptr() as *const u8, data.len() * size_of::<$data_type>()) })
                } else {
                    // Endianness flip is necessary
                    for data_index in 0..data.len() {
                        let start_index = data_index * size_of::<$data_type>();
                        let bytes_slice = &mut bytes[start_index..(start_index + size_of::<$data_type>())];
                        bytes_slice.copy_from_slice(&self.[<$data_type _to_bytes>](data[data_index]));
                    }
                }
            }
        }
    };
}
impl DataEndianness {
    pub fn host_endianness() -> DataEndianness {
        if cfg!(target_endian = "big") {
            DataEndianness::BigEndian
        } else {
            DataEndianness::LittleEndian
        }
    }
    impl_endian_aware_type!(u16);
    impl_endian_aware_type!(u32);
    impl_endian_aware_type!(u64);
    impl_endian_aware_type!(i16);
    impl_endian_aware_type!(i32);
    impl_endian_aware_type!(i64);
    impl_endian_aware_type!(f32);
    impl_endian_aware_type!(f64);
}

macro_rules! impl_memory_access {
    ($data_type: ident) => {
        paste! {
            fn [<read_ $data_type>](&self, address: u64) -> anyhow::Result<$data_type> {
                let endianness = self.data_endianness();
                let mut buffer: [u8; size_of::<$data_type>()] = [0; size_of::<$data_type>()];
                self.read_chunk(address, &mut buffer)?;
                Ok(endianness.[<$data_type _from_bytes>](buffer))
            }
            fn [<read_ $data_type _array>](&self, address: u64, buffer: &mut [$data_type]) -> anyhow::Result<()> {
                let endianness = self.data_endianness();
                let mut byte_buffer: Box<[u8]> = vec![0; buffer.len() * size_of::<$data_type>()].into_boxed_slice();
                self.read_chunk(address, byte_buffer.deref_mut())?;
                endianness.[<$data_type _array_from_bytes>](&*byte_buffer, buffer);
                Ok({})
            }
            fn [<write_ $data_type>](&self, address: u64, value: $data_type) -> anyhow::Result<()> {
                let endianness = self.data_endianness();
                let buffer: [u8; size_of::<$data_type>()] = endianness.[<$data_type _to_bytes>](value);
                self.write_chunk(address, &buffer)
            }
            fn [<write_ $data_type _array>](&self, address: u64, buffer: &[$data_type]) -> anyhow::Result<()> {
                let endianness = self.data_endianness();
                let mut byte_buffer: Box<[u8]> = vec![0; buffer.len() * size_of::<$data_type>()].into_boxed_slice();
                endianness.[<$data_type _array_to_bytes>](buffer, byte_buffer.deref_mut());
                self.write_chunk(address, byte_buffer.deref())
            }
        }
    }
}

/// Interface for reading and writing memory at arbitrary addresses. Address in this context can refer to either relative or absolute address located within this process or another process address space
pub trait Memory {
    /// Returns the address width in bytes for the memory backend. Address width determines the size of the pointer type
    fn address_width(&self) -> usize;
    /// Returns the endianness of this memory backend
    fn data_endianness(&self) -> DataEndianness;

    impl_memory_access!(u16);
    impl_memory_access!(u32);
    impl_memory_access!(u64);
    impl_memory_access!(i16);
    impl_memory_access!(i32);
    impl_memory_access!(i64);
    impl_memory_access!(f32);
    impl_memory_access!(f64);

    fn read_u8(&self, address: u64) -> anyhow::Result<u8> {
        let mut buffer: [u8; 1] = [0; 1];
        self.read_chunk(address, &mut buffer)?;
        Ok(buffer[0])
    }
    fn read_u8_array(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        self.read_chunk(address, buffer)
    }
    fn read_i8(&self, address: u64) -> anyhow::Result<i8> {
        let mut buffer: [u8; 1] = [0; 1];
        self.read_chunk(address, &mut buffer)?;
        Ok(buffer[0] as i8)
    }
    fn read_i8_array(&self, address: u64, buffer: &mut [i8]) -> anyhow::Result<()> {
        self.read_chunk(address, unsafe { &mut *slice_from_raw_parts_mut(buffer.as_ptr() as *mut u8, buffer.len()) })
    }
    fn read_raw_ptr(&self, address: u64) -> anyhow::Result<u64> {
        match self.address_width() {
            8 => Ok(self.read_u64(address)?),
            4 => Ok(self.read_u32(address)? as u64),
            _ => panic!("Unsupported address width")
        }
    }
    fn read_raw_ptr_array(&self, address: u64, buffer: &mut [u64]) -> anyhow::Result<()> {
        match self.address_width() {
            8 => Ok(self.read_u64_array(address, buffer)?),
            4 => {
                let mut raw_address_buffer: Box<[u32]> = vec![0; buffer.len()].into_boxed_slice();
                self.read_u32_array(address, raw_address_buffer.deref_mut())?;
                for pointer_index in 0..buffer.len() {
                    buffer[pointer_index] = raw_address_buffer[pointer_index] as u64;
                }
                Ok({})
            },
            _ => panic!("Unsupported address width")
        }
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()>;

    fn write_u8(&self, address: u64, value: u8) -> anyhow::Result<()> {
        let buffer: [u8; 1] = [value];
        self.write_chunk(address, &buffer)
    }
    fn write_u8_array(&self, address: u64, buffer: &[u8]) -> anyhow::Result<()> {
        self.write_chunk(address, buffer)
    }
    fn write_i8(&self, address: u64, value: i8) -> anyhow::Result<()> {
        let buffer: [u8; 1] = [value as u8];
        self.write_chunk(address, &buffer)
    }
    fn write_i8_array(&self, address: u64, buffer: &[i8]) -> anyhow::Result<()> {
        self.write_chunk(address, unsafe { &*slice_from_raw_parts(buffer.as_ptr() as *const u8, buffer.len()) })
    }
    fn write_raw_ptr(&self, address: u64, value: u64) -> anyhow::Result<()> {
        match self.address_width() {
            8 => self.write_u64(address, value),
            4 => self.write_u32(address, value as u32),
            _ => panic!("Unsupported address width")
        }
    }
    fn write_raw_ptr_array(&self, address: u64, buffer: &[u64]) -> anyhow::Result<()> {
        match self.address_width() {
            8 => self.write_u64_array(address, buffer),
            4 => {
                let mut raw_address_buffer: Box<[u32]> = vec![0; buffer.len()].into_boxed_slice();
                for pointer_index in 0..buffer.len() {
                    raw_address_buffer[pointer_index] = buffer[pointer_index] as u32;
                }
                self.write_u32_array(address, raw_address_buffer.deref())
            },
            _ => panic!("Unsupported address width")
        }
    }
    fn write_chunk(&self, address: u64, buffer: &[u8]) -> anyhow::Result<()>;
}

/// Opaque pointer represents a pointer to memory at specific address
pub struct OpaquePtr<M: Memory> {
    pub memory: Arc<M>,
    pub address: u64,
}
impl<M: Memory> Clone for OpaquePtr<M> {
    fn clone(&self) -> Self {
        Self {
            memory: self.memory.clone(),
            address: self.address,
        }
    }
}
impl<M: Memory> PartialEq for OpaquePtr<M> {
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address && Arc::ptr_eq(&self.memory, &other.memory)
    }
}
impl<M: Memory> Eq for OpaquePtr<M> {}
impl<M: Memory> PartialOrd for OpaquePtr<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.address.partial_cmp(&other.address)
    }
}
impl<M: Memory> Ord for OpaquePtr<M> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.address.cmp(&other.address)
    }
}
impl<M: Memory> Hash for OpaquePtr<M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.address.hash(state)
    }
}
impl<M: Memory> Add<i64> for OpaquePtr<M> {
    type Output = Self;
    fn add(self, rhs: i64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add_signed(rhs).unwrap()}
    }
}
impl<M: Memory> Add<u64> for OpaquePtr<M> {
    type Output = Self;
    fn add(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add(rhs).unwrap()}
    }
}
impl<M: Memory> Add<usize> for OpaquePtr<M> {
    type Output = Self;
    fn add(self, rhs: usize) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add(rhs as u64).unwrap()}
    }
}
impl<M: Memory> Sub<u64> for OpaquePtr<M> {
    type Output = Self;
    fn sub(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub(rhs).unwrap()}
    }
}
impl<M: Memory> Sub<usize> for OpaquePtr<M> {
    type Output = Self;
    fn sub(self, rhs: usize) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub(rhs as u64).unwrap()}
    }
}
impl<M: Memory> OpaquePtr<M> {
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    pub fn is_nullptr(&self) -> bool {
        self.address == 0
    }
    /// Reads data of various sizes from the memory location pointed to by this pointer
    pub fn read_u8(&self) -> anyhow::Result<u8> { self.memory.read_u8(self.address) }
    pub fn read_u8_array(&self, buffer: &mut [u8]) -> anyhow::Result<()> { self.memory.read_u8_array(self.address, buffer) }
    pub fn read_u16(&self) -> anyhow::Result<u16> { self.memory.read_u16(self.address) }
    pub fn read_u16_array(&self, buffer: &mut [u16]) -> anyhow::Result<()> { self.memory.read_u16_array(self.address, buffer) }
    pub fn read_u32(&self) -> anyhow::Result<u32> { self.memory.read_u32(self.address) }
    pub fn read_u32_array(&self, buffer: &mut [u32]) -> anyhow::Result<()> { self.memory.read_u32_array(self.address, buffer) }
    pub fn read_u64(&self) -> anyhow::Result<u64> { self.memory.read_u64(self.address) }
    pub fn read_u64_array(&self, buffer: &mut [u64]) -> anyhow::Result<()> { self.memory.read_u64_array(self.address, buffer) }
    pub fn read_i8(&self) -> anyhow::Result<i8> { self.memory.read_i8(self.address) }
    pub fn read_i8_array(&self, buffer: &mut [i8]) -> anyhow::Result<()> { self.memory.read_i8_array(self.address, buffer) }
    pub fn read_i16(&self) -> anyhow::Result<i16> { self.memory.read_i16(self.address) }
    pub fn read_i16_array(&self, buffer: &mut [i16]) -> anyhow::Result<()> { self.memory.read_i16_array(self.address, buffer) }
    pub fn read_i32(&self) -> anyhow::Result<i32> { self.memory.read_i32(self.address) }
    pub fn read_i32_array(&self, buffer: &mut [i32]) -> anyhow::Result<()> { self.memory.read_i32_array(self.address, buffer) }
    pub fn read_i64(&self) -> anyhow::Result<i64> { self.memory.read_i64(self.address) }
    pub fn read_i64_array(&self, buffer: &mut [i64]) -> anyhow::Result<()> { self.memory.read_i64_array(self.address, buffer) }
    pub fn read_f32(&self) -> anyhow::Result<f32> { self.memory.read_f32(self.address) }
    pub fn read_f32_array(&self, buffer: &mut [f32]) -> anyhow::Result<()> { self.memory.read_f32_array(self.address, buffer) }
    pub fn read_f64(&self) -> anyhow::Result<f64> { self.memory.read_f64(self.address) }
    pub fn read_f64_array(&self, buffer: &mut [f64]) -> anyhow::Result<()> { self.memory.read_f64_array(self.address, buffer) }
    pub fn read_ptr(&self) -> anyhow::Result<Self> { Ok(OpaquePtr{memory: self.memory.clone(), address: self.memory.read_raw_ptr(self.address)?}) }
    pub fn read_ptr_array(&self, len: usize) -> anyhow::Result<Vec<Self>> {
        let mut result: Vec<Self> = Vec::with_capacity(len);
        let mut raw_ptr_buffer: Box<[u64]> = vec![0; len].into_boxed_slice();
        self.memory.read_u64_array(self.address, raw_ptr_buffer.deref_mut())?;
        for pointer_index in 0..len {
            result.push(OpaquePtr{memory: self.memory.clone(), address: raw_ptr_buffer[pointer_index]});
        }
        Ok(result)
    }
    pub fn read_chunk(&self, buffer: &mut [u8]) -> anyhow::Result<()> { self.memory.read_chunk(self.address, buffer) }
    /// Writes data of various sizes to the memory location pointed to by this pointer
    pub fn write_u8(&self, value: u8) -> anyhow::Result<()> { self.memory.write_u8(self.address, value) }
    pub fn write_u8_array(&self, buffer: &[u8]) -> anyhow::Result<()> { self.memory.write_u8_array(self.address, buffer) }
    pub fn write_u16(&self, value: u16) -> anyhow::Result<()> { self.memory.write_u16(self.address, value) }
    pub fn write_u16_array(&self, buffer: &[u16]) -> anyhow::Result<()> { self.memory.write_u16_array(self.address, buffer) }
    pub fn write_u32(&self, value: u32) -> anyhow::Result<()> { self.memory.write_u32(self.address, value) }
    pub fn write_u32_array(&self, buffer: &[u32]) -> anyhow::Result<()> { self.memory.write_u32_array(self.address, buffer) }
    pub fn write_u64(&self, value: u64) -> anyhow::Result<()> { self.memory.write_u64(self.address, value) }
    pub fn write_u64_array(&self, buffer: &[u64]) -> anyhow::Result<()> { self.memory.write_u64_array(self.address, buffer) }
    pub fn write_i8(&self, value: i8) -> anyhow::Result<()> { self.memory.write_i8(self.address, value) }
    pub fn write_i8_array(&self, buffer: &[i8]) -> anyhow::Result<()> { self.memory.write_i8_array(self.address, buffer) }
    pub fn write_i16(&self, value: i16) -> anyhow::Result<()> { self.memory.write_i16(self.address, value) }
    pub fn write_i16_array(&self, buffer: &[i16]) -> anyhow::Result<()> { self.memory.write_i16_array(self.address, buffer) }
    pub fn write_i32(&self, value: i32) -> anyhow::Result<()> { self.memory.write_i32(self.address, value) }
    pub fn write_i32_array(&self, buffer: &[i32]) -> anyhow::Result<()> { self.memory.write_i32_array(self.address, buffer) }
    pub fn write_i64(&self, value: i64) -> anyhow::Result<()> { self.memory.write_i64(self.address, value) }
    pub fn write_i64_array(&self, buffer: &[i64]) -> anyhow::Result<()> { self.memory.write_i64_array(self.address, buffer) }
    pub fn write_f32(&self, value: f32) -> anyhow::Result<()> { self.memory.write_f32(self.address, value) }
    pub fn write_f32_array(&self, buffer: &[f32]) -> anyhow::Result<()> { self.memory.write_f32_array(self.address, buffer) }
    pub fn write_f64(&self, value: f64) -> anyhow::Result<()> { self.memory.write_f64(self.address, value) }
    pub fn write_f64_array(&self, buffer: &[f64]) -> anyhow::Result<()> { self.memory.write_f64_array(self.address, buffer) }
    pub fn write_ptr(&self, value: &Self) -> anyhow::Result<()> { self.memory.write_raw_ptr(self.address, value.address) }
    pub fn write_nullptr(&self) -> anyhow::Result<()> { self.memory.write_raw_ptr(self.address, 0) }
    pub fn write_ptr_array(&self, buffer: &[Self]) -> anyhow::Result<()> {
        let mut raw_ptr_buffer: Box<[u64]> = vec![0; buffer.len()].into_boxed_slice();
        for pointer_index in 0..buffer.len() {
            raw_ptr_buffer[pointer_index] = buffer[pointer_index].address;
        }
        self.memory.write_raw_ptr_array(self.address, raw_ptr_buffer.deref())
    }
    pub fn write_chunk(&self, value: &[u8]) -> anyhow::Result<()> { self.memory.write_chunk(self.address, value) }
}
