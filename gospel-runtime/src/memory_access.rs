use std::cmp::{Ordering};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Add, Receiver, Sub};

/// Interface for reading and writing memory at arbitrary addresses. Address in this context can refer to either relative or absolute address located within this process or another process address space
pub trait Memory: Clone {
    fn read_u8(&self, address: u64) -> anyhow::Result<u8>;
    fn read_u16(&self, address: u64) -> anyhow::Result<u16>;
    fn read_u32(&self, address: u64) -> anyhow::Result<u32>;
    fn read_u64(&self, address: u64) -> anyhow::Result<u64>;
    fn read_raw_ptr(&self, address: u64) -> anyhow::Result<u64>;
    fn read_chunk(&self, address: u64, size: usize) -> anyhow::Result<Vec<u8>>;

    fn write_u8(&self, address: u64, value: u8) -> anyhow::Result<()>;
    fn write_u16(&self, address: u64, value: u16) -> anyhow::Result<()>;
    fn write_u32(&self, address: u64, value: u32) -> anyhow::Result<()>;
    fn write_u64(&self, address: u64, value: u64) -> anyhow::Result<()>;
    fn write_raw_ptr(&self, address: u64, value: u64) -> anyhow::Result<()>;
    fn write_chunk(&self, address: u64, value: &[u8]) -> anyhow::Result<()>;
}

/// Opaque pointer represents a pointer to memory at specific address
#[derive(Clone, Eq, Ord)]
pub struct OpaquePtr<M : Memory> {
    pub memory: M,
    pub address: u64,
}
impl<M : Memory> PartialEq for OpaquePtr<M> {
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address
    }
}
impl<M : Memory> PartialOrd for OpaquePtr<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.address.partial_cmp(&other.address)
    }
}
impl<M : Memory> Hash for OpaquePtr<M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.address.hash(state)
    }
}
impl<M : Memory> Add<i64> for OpaquePtr<M> {
    type Output = OpaquePtr<M>;
    fn add(self, rhs: i64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add_signed(rhs).unwrap()}
    }
}
impl<M : Memory> Add<u64> for OpaquePtr<M> {
    type Output = OpaquePtr<M>;
    fn add(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_add(rhs).unwrap()}
    }
}
impl<M : Memory> Sub<i64> for OpaquePtr<M> {
    type Output = OpaquePtr<M>;
    fn sub(self, rhs: i64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub_signed(rhs).unwrap()}
    }
}
impl<M : Memory> Sub<u64> for OpaquePtr<M> {
    type Output = OpaquePtr<M>;
    fn sub(self, rhs: u64) -> Self::Output {
        Self{memory: self.memory, address: self.address.checked_sub(rhs).unwrap()}
    }
}
impl<M : Memory> OpaquePtr<M> {
    /// Reads data of various sizes from the memory location pointed to by this pointer
    pub fn read_u8(&self) -> anyhow::Result<u8> { self.memory.read_u8(self.address) }
    pub fn read_u16(&self) -> anyhow::Result<u16> { self.memory.read_u16(self.address) }
    pub fn read_u32(&self) -> anyhow::Result<u32> { self.memory.read_u32(self.address) }
    pub fn read_u64(&self) -> anyhow::Result<u64> { self.memory.read_u64(self.address) }
    pub fn read_ptr(&self) -> anyhow::Result<OpaquePtr<M>> { Ok(OpaquePtr{memory: self.memory.clone(), address: self.memory.read_raw_ptr(self.address)?}) }
    pub fn read_chunk(&self, size: usize) -> anyhow::Result<Vec<u8>> { self.memory.read_chunk(self.address, size) }
    /// Writes data of various sizes to the memory location pointed to by this pointer
    pub fn write_u8(&self, value: u8) -> anyhow::Result<()> { self.memory.write_u8(self.address, value) }
    pub fn write_u16(&self, value: u16) -> anyhow::Result<()> { self.memory.write_u16(self.address, value) }
    pub fn write_u32(&self, value: u32) -> anyhow::Result<()> { self.memory.write_u32(self.address, value) }
    pub fn write_u64(&self, value: u64) -> anyhow::Result<()> { self.memory.write_u64(self.address, value) }
    pub fn write_ptr(&self, value: &OpaquePtr<M>) -> anyhow::Result<()> { self.memory.write_raw_ptr(self.address, value.address) }
    pub fn write_chunk(&self, value: &[u8]) -> anyhow::Result<()> { self.memory.write_chunk(self.address, value) }
}

/// Typed pointer is a pointer to the value of the given type at a specified address
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypedPtr<M : Memory, T : ?Sized> {
    pub opaque_ptr: OpaquePtr<M>,
    phantom_data: PhantomData<T>,
}
impl<M : Memory, T : ?Sized> TypedPtr<M, T> {
    /// Constructs typed pointer from opaque pointer without performing any type checks
    pub fn from_opaque_unchecked(opaque_ptr: OpaquePtr<M>) -> Self {
        Self{opaque_ptr, phantom_data: PhantomData::default()}
    }
}
impl<M : Memory, T : ?Sized> Receiver for TypedPtr<M, T> {
    type Target = T;
}

/// Implemented for trivial types that can be directly read and written from typed ptr
pub trait TrivialValue<M : Memory> : Copy + Sized {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self>;
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()>;
}
impl<M : Memory> TrivialValue<M> for u8 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { self.opaque_ptr.read_u8() }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u8(value) }
}
impl<M : Memory> TrivialValue<M> for u16 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { self.opaque_ptr.read_u16() }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u16(value) }
}
impl<M : Memory> TrivialValue<M> for u32 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { self.opaque_ptr.read_u32() }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u32(value) }
}
impl<M : Memory> TrivialValue<M> for u64 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { self.opaque_ptr.read_u64() }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u64(value) }
}
impl<M : Memory> TrivialValue<M> for i8 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(self.opaque_ptr.read_u8()? as i8) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u8(value as u8) }
}
impl<M : Memory> TrivialValue<M> for i16 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(self.opaque_ptr.read_u16()? as i16) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u16(value as u16) }
}
impl<M : Memory> TrivialValue<M> for i32 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(self.opaque_ptr.read_u32()? as i32) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u32(value as u32) }
}
impl<M : Memory> TrivialValue<M> for i64 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(self.opaque_ptr.read_u64()? as i64) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u64(value as u64) }
}
impl<M : Memory> TrivialValue<M> for f32 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(f32::from_bits(self.opaque_ptr.read_u32()?)) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u32(value.to_bits()) }
}
impl<M : Memory> TrivialValue<M> for f64 {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<Self> { Ok(f64::from_bits(self.opaque_ptr.read_u64()?)) }
    fn write(self: &TypedPtr<M, Self>, value: Self) -> anyhow::Result<()> { self.opaque_ptr.write_u64(value.to_bits()) }
}

/// Implemented for pointer-like types that can be read and written as pointers
pub trait PointerValue<M : Memory, T : ?Sized> : Sized {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<TypedPtr<M, T>>;
    fn write(self: &TypedPtr<M, Self>, value: &TypedPtr<M, T>) -> anyhow::Result<()>;
}
impl<M : Memory, T : ?Sized> PointerValue<M, T> for TypedPtr<M, T> {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<TypedPtr<M, T>> { Ok(TypedPtr::from_opaque_unchecked(self.opaque_ptr.read_ptr()?)) }
    fn write(self: &TypedPtr<M, Self>, value: &TypedPtr<M, T>) -> anyhow::Result<()> { self.opaque_ptr.write_ptr(&value.opaque_ptr) }
}
impl<M : Memory, T : ?Sized> PointerValue<M, T> for &T {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<TypedPtr<M, T>> { Ok(TypedPtr::from_opaque_unchecked(self.opaque_ptr.read_ptr()?)) }
    fn write(self: &TypedPtr<M, Self>, value: &TypedPtr<M, T>) -> anyhow::Result<()> { self.opaque_ptr.write_ptr(&value.opaque_ptr) }
}
impl<M : Memory, T : ?Sized> PointerValue<M, T> for &mut T {
    fn read(self: &TypedPtr<M, Self>) -> anyhow::Result<TypedPtr<M, T>> { Ok(TypedPtr::from_opaque_unchecked(self.opaque_ptr.read_ptr()?)) }
    fn write(self: &TypedPtr<M, Self>, value: &TypedPtr<M, T>) -> anyhow::Result<()> { self.opaque_ptr.write_ptr(&value.opaque_ptr) }
}
