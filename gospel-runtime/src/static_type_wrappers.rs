use std::ops::{Deref, DerefMut, Receiver};
use anyhow::bail;
use std::marker::PhantomData;
use anyhow::anyhow;
use paste::paste;
use crate::{memory_access::Memory, runtime_type_model::{DynamicPtr, TypePtrMetadata, TypePtrNamespace}};
use gospel_typelib::type_model::{ArrayType, PointerType, PrimitiveType, Type};
use crate::memory_access::OpaquePtr;

/// Represents a value corresponding to native type "long int", which can have a size of either 4 or 8 bytes depending on the target
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LongInt(i64);

/// Represents a value corresponding to native type "unsigned long int", which can have a size of either 4 or 8 bytes depending on the target
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UnsignedLongInt(u64);

/// Represents a value corresponding to native type "wchar_t", which can have a size of either 2 or 4 bytes depending on the target
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WideChar(u32);

/// Implemented on the types that do not have enough information in compile time to create a static type, but can still be used with typed pointers
pub trait DynamicTypeTag {
    /// Given the pointer to the cast source, attempts to determine the index of the type that the cast should be performed to
    /// Return None to indicate that casting from the provided type to this type is not possible
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize>;
}

/// Implemented on the types that have identity and can be represented in a type namespace
pub trait StaticTypeTag : DynamicTypeTag {
    /// Stores type descriptor for this type in the provided type namespace and returns the pointer to it
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize;
}

/// Implemented by POD types that can be trivially copied from/to the process memory as a sequence of bytes
pub trait TrivialValue : StaticTypeTag + Default + Clone {
    fn static_read<M: Memory>(ptr: &DynamicPtr<M>) -> anyhow::Result<Self>;
    fn static_write<M: Memory>(ptr: &DynamicPtr<M>, value: Self) -> anyhow::Result<()>;
    fn static_read_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &mut [Self]) -> anyhow::Result<()>;
    fn static_write_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &[Self]) -> anyhow::Result<()>;
}

macro_rules! implement_numeric_trivial_value {
    ( $value_type:ident, $primitive_type:expr) => {
       impl StaticTypeTag for $value_type {
            fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
                let mut type_graph = namespace.type_graph.write().unwrap();
                type_graph.store_type(Type::Primitive($primitive_type))
            }
       }
       impl DynamicTypeTag for $value_type {
            fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
                Some(Self::store_type_descriptor(&ptr_metadata.namespace))
            }
       }
       impl TrivialValue for $value_type {
            fn static_read<M: Memory>(ptr: &DynamicPtr<M>) -> anyhow::Result<Self> {
                paste! {
                    ptr.[<read_ $value_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                }
            }
            fn static_write<M: Memory>(ptr: &DynamicPtr<M>, value: Self) -> anyhow::Result<()> {
                paste! {
                    ptr.[<write_ $value_type>](value)
                }
            }
            fn static_read_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                 paste! {
                    if !ptr.[<read_ $value_type _slice_unchecked>](buffer)? {
                        Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    } else { Ok({}) }
                }
            }
            fn static_write_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &[$value_type]) -> anyhow::Result<()> {
                paste! {
                    ptr.[<write_ $value_type _slice_unchecked>](buffer)
                }
            }
        }
    };
}
implement_numeric_trivial_value!(u8, PrimitiveType::UnsignedChar);
implement_numeric_trivial_value!(u16, PrimitiveType::UnsignedShortInt);
implement_numeric_trivial_value!(u32, PrimitiveType::UnsignedInt);
implement_numeric_trivial_value!(u64, PrimitiveType::UnsignedLongLongInt);
implement_numeric_trivial_value!(i8, PrimitiveType::Char);
implement_numeric_trivial_value!(i16, PrimitiveType::ShortInt);
implement_numeric_trivial_value!(i32, PrimitiveType::Int);
implement_numeric_trivial_value!(i64, PrimitiveType::LongLongInt);
implement_numeric_trivial_value!(f32, PrimitiveType::Float);
implement_numeric_trivial_value!(f64, PrimitiveType::Double);

macro_rules! implement_variable_size_trivial_value {
    ( $value_type:ident, $large_underlying_type:ident, $small_underlying_type:ident, $primitive_type:expr) => {
        paste! {
            impl StaticTypeTag for $value_type {
                fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
                    let mut type_graph = namespace.type_graph.write().unwrap();
                    type_graph.store_type(Type::Primitive($primitive_type))
                }
            }
            impl DynamicTypeTag for $value_type {
                fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
                    Some(Self::store_type_descriptor(&ptr_metadata.namespace))
                }
            }
            impl TrivialValue for $value_type {
                fn static_read<M: Memory>(ptr: &DynamicPtr<M>) -> anyhow::Result<Self> {
                    let (_, primitive_size) = ptr.metadata.primitive_type_and_size().unwrap();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        Ok($value_type(ptr.[<read_ $small_underlying_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))? as $large_underlying_type))
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        Ok($value_type(ptr.[<read_ $large_underlying_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))? as $large_underlying_type))
                    } else {
                        Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn static_write<M: Memory>(ptr: &DynamicPtr<M>, value: Self) -> anyhow::Result<()> {
                   let (_, primitive_size) = ptr.metadata.primitive_type_and_size().unwrap();
                   if primitive_size == size_of::<$small_underlying_type>() {
                       ptr.[<write_ $small_underlying_type>](value.0 as $small_underlying_type)
                   } else if primitive_size == size_of::<$large_underlying_type>() {
                       ptr.[<write_ $large_underlying_type>](value.0 as $large_underlying_type)
                   } else {
                       Err(anyhow!("Failed to write: value is not compatible with {} type", core::stringify!($value_type)))
                   }
                }
                fn static_read_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                    let (_, primitive_size) = ptr.metadata.primitive_type_and_size().unwrap();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        if !ptr.[<read_ $small_underlying_type _slice_unchecked>](local_buffer.deref_mut())? {
                            bail!("Failed to read: value is not compatible with {} type", core::stringify!($value_type));
                        }
                        for index in 0..buffer.len() {
                            buffer[index] = $value_type(local_buffer[index] as $large_underlying_type)
                        }
                        Ok({})
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        if !ptr.[<read_ $large_underlying_type _slice_unchecked>](local_buffer.deref_mut())? {
                            bail!("Failed to read: value is not compatible with {} type", core::stringify!($value_type));
                        }
                        for index in 0..buffer.len() {
                            buffer[index] = $value_type(local_buffer[index] as $large_underlying_type)
                        }
                        Ok({})
                    } else {
                       Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn static_write_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                    let (_, primitive_size) = ptr.metadata.primitive_type_and_size().unwrap();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $small_underlying_type;
                        }
                        ptr.[<write_ $small_underlying_type _slice_unchecked>](local_buffer.deref())
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $large_underlying_type;
                        }
                        ptr.[<write_ $large_underlying_type _slice_unchecked>](local_buffer.deref())
                    } else {
                       Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
            }
        }
    };
}

implement_variable_size_trivial_value!(LongInt, i64, i32, PrimitiveType::LongInt);
implement_variable_size_trivial_value!(UnsignedLongInt, u64, u32, PrimitiveType::UnsignedLongInt);
implement_variable_size_trivial_value!(WideChar, u32, u16, PrimitiveType::WideChar);

/// Trait implemented by the types that are allowed to appear as underlying types for enums
pub trait EnumUnderlyingType where Self : Sized {
    /// Converts value of this type to the raw 64-bit discriminant
    fn to_raw_discriminant(self) -> u64;
    /// Constructs value of this type from the raw 64-bit discriminant
    fn from_raw_discriminant(raw_discriminant: u64) -> Self;
}

macro_rules! implement_integral_enum_underlying_type {
    ($value_type:ty) => {
        impl EnumUnderlyingType for $value_type {
            fn to_raw_discriminant(self) -> u64 { self as u64 }
            fn from_raw_discriminant(raw_discriminant: u64) -> Self { raw_discriminant as $value_type }
        }
    };
}
implement_integral_enum_underlying_type!(u8 );
implement_integral_enum_underlying_type!(u16);
implement_integral_enum_underlying_type!(u32);
implement_integral_enum_underlying_type!(u64);
implement_integral_enum_underlying_type!(i8 );
implement_integral_enum_underlying_type!(i16);
implement_integral_enum_underlying_type!(i32);
implement_integral_enum_underlying_type!(i64);

impl EnumUnderlyingType for UnsignedLongInt {
    fn to_raw_discriminant(self) -> u64 { self.0 }
    fn from_raw_discriminant(raw_discriminant: u64) -> Self { Self(raw_discriminant) }
}
impl EnumUnderlyingType for LongInt {
    fn to_raw_discriminant(self) -> u64 { self.0 as u64 }
    fn from_raw_discriminant(raw_discriminant: u64) -> Self { Self(raw_discriminant as i64) }
}
impl EnumUnderlyingType for WideChar {
    fn to_raw_discriminant(self) -> u64 { self.0 as u64 }
    fn from_raw_discriminant(raw_discriminant: u64) -> Self { Self(raw_discriminant as u32) }
}

impl StaticTypeTag for bool {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
        let mut type_graph = namespace.type_graph.write().unwrap();
        type_graph.store_type(Type::Primitive(PrimitiveType::Bool))
    }
}
impl DynamicTypeTag for bool {
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
        Some(Self::store_type_descriptor(&ptr_metadata.namespace))
    }
}
impl TrivialValue for bool {
    fn static_read<M: Memory>(ptr: &DynamicPtr<M>) -> anyhow::Result<Self> {
        Ok(ptr.read_u8()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with bool type"))? != 0)
    }
    fn static_write<M: Memory>(ptr: &DynamicPtr<M>, value: Self) -> anyhow::Result<()> {
        ptr.write_u8(if value { 1 } else { 0 })
    }
    fn static_read_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        if !ptr.read_u8_slice_unchecked(byte_buffer.deref_mut())? {
            bail!("Failed to read: value is not compatible with bool type");
        }
        for index in 0..buffer.len() {
            buffer[index] = byte_buffer[index] != 0;
        }
        Ok({})
    }
    fn static_write_slice_unchecked<M: Memory>(ptr: &DynamicPtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        for index in 0..buffer.len() {
            byte_buffer[index] = if buffer[index] { 1 } else { 0 };
        }
        ptr.write_u8_slice_unchecked(byte_buffer.deref())
    }
}

/// Implementation of StaticTypeTag for Unit type. Unit type maps to void type in C/C++
impl StaticTypeTag for () {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
        let mut type_graph = namespace.type_graph.write().unwrap();
        type_graph.store_type(Type::Primitive(PrimitiveType::Void))
    }
}
impl DynamicTypeTag for () {
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
        Some(Self::store_type_descriptor(&ptr_metadata.namespace))
    }
}

/// Represents a unit type used to refer to C++ statically sized array type with the given element type
pub struct StaticArray<T : DynamicTypeTag + ?Sized> {
    phantom_data: PhantomData<T>,
    _dynamic_size_marker: [u8],
}
impl<T : DynamicTypeTag + ?Sized> DynamicTypeTag for StaticArray<T> {
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
        // Check that this is a statically sized array type
        let element_type_index = ptr_metadata.array_element_type_index()?;
        let array_length = ptr_metadata.array_static_array_length()?;

        // Create pointer metadata for element type and determine what type our static element type wants to cast to
        let array_element_ptr_metadata = ptr_metadata.with_type_index(element_type_index);
        let cast_element_type_index = T::get_cast_target_type_descriptor(&array_element_ptr_metadata)?;

        // Create and store new array type with the same length as this array but with the desired cast target element type
        let mut type_graph = ptr_metadata.namespace.type_graph.write().unwrap();
        Some(type_graph.store_type(Type::Array(ArrayType{element_type_index: cast_element_type_index, array_length})))
    }
}
impl<T : StaticTypeTag + ?Sized> StaticArray<T> {
    pub fn from_raw_ptr<M : Memory>(ptr: OpaquePtr<M>, namespace: &TypePtrNamespace, array_length: usize) -> Ptr<M, Self> {
        let type_index = Self::store_type_descriptor(namespace, array_length);
        Ptr::from_ptr_unchecked(DynamicPtr{opaque_ptr: ptr, metadata: TypePtrMetadata{namespace: namespace.clone(), type_index}})
    }
    pub fn store_type_descriptor(namespace: &TypePtrNamespace, array_length: usize) -> usize {
        let element_type_index = T::store_type_descriptor(namespace);
        let mut type_graph = namespace.type_graph.write().unwrap();
        type_graph.store_type(Type::Array(ArrayType{element_type_index, array_length}))
    }
}

/// Represents a non-null pointer to a value of type T. This is similar to NonNull<T> type in standard library
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ref<M : Memory, T : DynamicTypeTag + ?Sized> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T : DynamicTypeTag + ?Sized> Ref<M, T> {
    /// Constructs a ptr from dynamic ptr without checking types or address of the given pointer. This is a dangerous function that should not be called manually
    pub fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    /// Casts reference of this type to reference of another type, returns None if cast is not possible
    pub fn cast<R : DynamicTypeTag + ?Sized>(&self) -> Option<Ref<M, R>> {
        Ref::<M, R>::do_static_cast(&self.inner_ptr)
    }
    /// Casts pointer of this type to reference of another type, returns an error if cast is not possible
    pub fn cast_checked<R : DynamicTypeTag + ?Sized>(&self) -> Ref<M, R> {
        self.cast::<R>().unwrap()
    }
    /// Offsets this reference towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        Self::from_ptr_unchecked(self.inner_ptr.add_unchecked(count))
    }
    /// Offsets this reference towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        Self::from_ptr_unchecked(self.inner_ptr.sub_unchecked(count))
    }
    /// Converts this reference to a pointer
    pub fn to_ptr(self) -> Ptr<M, T> {
        Ptr::from_ptr_unchecked(self.inner_ptr)
    }
    /// Attempts to cast the given dynamic pointer to this reference type. Will return None if types are unrelated or provided ptr points to null
    fn do_static_cast(ptr: &DynamicPtr<M>) -> Option<Self> {
        if let Some(ptr) = Ptr::<M, T>::do_static_cast(ptr) && !ptr.is_nullptr() {
            Some(Self::from_ptr_unchecked(ptr.inner_ptr))
        } else { None }
    }
}
/// Receiver implementation so that Ref type can be used to dispatch functions on the pointee
impl<M : Memory, T : DynamicTypeTag + ?Sized> Receiver for Ref<M, T> {
    type Target = T;
}
/// Static type implementation for references to static types
impl<M : Memory, T : StaticTypeTag + ?Sized> StaticTypeTag for Ref<M, T> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
        let pointee_type_index = T::store_type_descriptor(namespace);
        let mut type_graph = namespace.type_graph.write().unwrap();
        type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: true}))
    }
}
impl<M : Memory, T : DynamicTypeTag + ?Sized> DynamicTypeTag for Ref<M, T> {
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
        let pointee_type_index = T::get_cast_target_type_descriptor(ptr_metadata)?;
        let mut type_graph = ptr_metadata.namespace.type_graph.write().unwrap();
        Some(type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: true})))
    }
}

impl<M : Memory, T : TrivialValue> Ref<M, T> {
    /// Reads the trivial value from the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<T> {
        T::static_read(&self.inner_ptr)
    }
    /// Writes the trivial value to the memory location pointed to by this reference
    pub fn write(&self, value: T) -> anyhow::Result<()> {
        T::static_write(&self.inner_ptr, value)
    }
    /// Reads the slice of trivial values from the memory location pointed to by this reference
    pub fn read_slice_unchecked(&self, len: usize) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); len];
        T::static_read_slice_unchecked(&self.inner_ptr, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    /// Writes the slice of trivial values to the memory location pointed to by this reference
    pub fn write_slice_unchecked(&self, slice: &[T]) -> anyhow::Result<()> {
        T::static_write_slice_unchecked(&self.inner_ptr, slice)
    }
}

impl<M : Memory, T : DynamicTypeTag + ?Sized> Ref<M, Ptr<M, T>> {
    /// Reads the pointer value at the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<Ptr<M, T>> {
        let result_ptr = self.inner_ptr.read_ptr()?.ok_or_else(|| anyhow!("Ptr does not point to a ptr"))?;
        Ok(Ptr::from_ptr_unchecked(result_ptr))
    }
    /// Writes the pointer value to the memory location pointed to by this reference
    pub fn write(&self, value: &Ptr<M, T>) -> anyhow::Result<()> {
        self.inner_ptr.write_ptr(&value.inner_ptr)
    }
    /// Writes null pointer value to the memory location pointed to by this reference
    pub fn write_nullptr(&self) -> anyhow::Result<()> {
        self.inner_ptr.write_nullptr()
    }
}

impl<M : Memory, T : DynamicTypeTag + ?Sized> Ref<M, Ref<M, T>> {
    /// Reads the reference value at the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<Ref<M, T>> {
        let result_ptr = self.inner_ptr.read_ptr()?.ok_or_else(|| anyhow!("Ptr does not point to a ptr"))?;
        Ok(Ref::from_ptr_unchecked(result_ptr))
    }
    /// Writes the reference value to the memory location pointed to by this reference
    pub fn write(&self, value: &Ref<M, T>) -> anyhow::Result<()> {
        self.inner_ptr.write_ptr(&value.inner_ptr)
    }
}

impl<M : Memory, T : DynamicTypeTag + ?Sized> Ref<M, StaticArray<T>> {
    /// Returns the length of this statically sized array
    pub fn static_len(&self) -> usize {
        self.inner_ptr.metadata.array_static_array_length().unwrap()
    }
    /// Returns the type pointer metadata for the pointee
    pub fn element_metadata(&self) -> TypePtrMetadata {
        self.inner_ptr.metadata.with_type_index(self.inner_ptr.metadata.array_element_type_index().unwrap())
    }
    /// Returns the pointer to the array element at index
    pub fn element_ptr(&self, index: usize) -> Ref<M, T> {
        Ref::from_ptr_unchecked(self.inner_ptr.get_array_element_ptr(index).unwrap())
    }
}

impl<M : Memory, T : TrivialValue> Ref<M, StaticArray<T>> {
    /// Reads the static array element value from memory location at given index
    pub fn read_element(&self, index: usize) -> anyhow::Result<T> {
        self.element_ptr(index).read()
    }
    /// Writes to the static array element memory location at given index
    pub fn write_element(&self, index: usize, value: T) -> anyhow::Result<()> {
        self.element_ptr(index).write(value)
    }
    /// Reads contents of the entire statically sized array into a vector
    pub fn read_array(&self) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); self.static_len()];
        T::static_read_slice_unchecked(&self.element_ptr(0).inner_ptr, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    /// Writes contents of the entire statically sized array from a slice
    pub fn write_array(&self, array: &[T]) -> anyhow::Result<()> {
        if self.static_len() != array.len() {
            bail!("Static array length mismatch: Array length is {}, but passed slice len is {}", self.static_len(), array.len());
        }
        T::static_write_slice_unchecked(&self.element_ptr(0).inner_ptr, array)
    }
}

/// Represents a pointer to the value of the given type that could potentially be null. This is similar to raw *ptr type
/// Note that memory location pointed to by Ptr type cannot be accessed directly
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ptr<M : Memory, T : DynamicTypeTag + ?Sized> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T : DynamicTypeTag + ?Sized> Ptr<M, T> {
    /// Constructs a ptr from dynamic ptr without checking for the requirements for the successful cast
    pub fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    pub fn cast<R : DynamicTypeTag + ?Sized>(&self) -> Option<Ptr<M, R>> {
        Ptr::<M, R>::do_static_cast(&self.inner_ptr)
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    pub fn cast_checked<R : DynamicTypeTag + ?Sized>(&self) -> Ptr<M, R> {
        self.cast::<R>().unwrap()
    }
    /// Casts pointer of this type to reference of given type, returns None if cast is not possible
    pub fn cast_ref<R: DynamicTypeTag + ?Sized>(&self) -> Option<Ref<M, R>> {
        Ref::<M, R>::do_static_cast(&self.inner_ptr)
    }
    /// Casts pointer of this type to reference of given type, returns an error if cast is not possible
    pub fn cast_ref_checked<R : DynamicTypeTag>(&self) -> Ref<M, R> {
        self.cast_ref::<R>().unwrap()
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        Self::from_ptr_unchecked(self.inner_ptr.add_unchecked(count))
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        Self::from_ptr_unchecked(self.inner_ptr.sub_unchecked(count))
    }
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    pub fn is_nullptr(&self) -> bool {
        self.inner_ptr.is_nullptr()
    }
    /// Converts this pointer to a reference. Returns None if the pointer has the value of null
    pub fn to_ref(self) -> Option<Ref<M, T>> {
        if !self.is_nullptr() { Some(Ref::from_ptr_unchecked(self.inner_ptr)) } else { None }
    }
    /// Converts this pointer to a reference. Panics if the pointer is null
    pub fn to_ref_checked(self) -> Ref<M, T> {
        self.to_ref().unwrap()
    }
    /// Attempts to cast the given dynamic pointer to this pointer type. Will return None if types are unrelated
    fn do_static_cast(ptr: &DynamicPtr<M>) -> Option<Self> {
        let type_index = T::get_cast_target_type_descriptor(&ptr.metadata)?;
        let type_adjust = ptr.metadata.namespace.get_static_cast_pointer_adjust(ptr.metadata.type_index, type_index)?;
        Some(Self::from_ptr_unchecked(DynamicPtr{
            opaque_ptr: ptr.opaque_ptr.clone() + type_adjust,
            metadata: ptr.metadata.with_type_index(type_index)
        }))
    }
}

/// Static type implementation for Ptr for pointers to static types
impl<M : Memory, T : StaticTypeTag + ?Sized> StaticTypeTag for Ptr<M, T> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> usize {
        let pointee_type_index = T::store_type_descriptor(namespace);
        let mut type_graph = namespace.type_graph.write().unwrap();
        type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: false}))
    }
}
impl<M : Memory, T : StaticTypeTag + ?Sized> Ptr<M, T> {
    pub fn from_raw_ptr(ptr: OpaquePtr<M>, namespace: &TypePtrNamespace) -> Ptr<M, T> {
        let type_index = T::store_type_descriptor(namespace);
        Ptr::from_ptr_unchecked(DynamicPtr{opaque_ptr: ptr, metadata: TypePtrMetadata{namespace: namespace.clone(), type_index}})
    }
}
impl<M : Memory, T : DynamicTypeTag + ?Sized> DynamicTypeTag for Ptr<M, T> {
    fn get_cast_target_type_descriptor(ptr_metadata: &TypePtrMetadata) -> Option<usize> {
        let pointee_type_index = T::get_cast_target_type_descriptor(ptr_metadata)?;
        let mut type_graph = ptr_metadata.namespace.type_graph.write().unwrap();
        Some(type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: false})))
    }
}

/// References can be freely converted to pointers
impl<M : Memory, T : DynamicTypeTag + ?Sized> From<Ref<M, T>> for Ptr<M, T> {
    fn from(value: Ref<M, T>) -> Self {
        value.to_ptr()
    }
}
/// Pointers can be converted to references if they are not null
impl<M : Memory, T : DynamicTypeTag + ?Sized> TryFrom<Ptr<M, T>> for Ref<M, T> {
    type Error = ();
    fn try_from(value: Ptr<M, T>) -> Result<Self, Self::Error> {
        value.to_ref().ok_or(())
    }
}

/// Additional functions on DynamicPtr for integration with statically typed Ptr and Ref
impl<M: Memory> DynamicPtr<M> {
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    pub fn cast<T : DynamicTypeTag + ?Sized>(&self) -> Option<Ptr<M, T>> {
        Ptr::<M, T>::do_static_cast(self)
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    pub fn cast_checked<T : DynamicTypeTag + ?Sized>(&self) -> Ptr<M, T> {
        self.cast::<T>().unwrap()
    }
    /// Casts pointer of this type to reference of given type, returns None if cast is not possible
    pub fn cast_ref<T : DynamicTypeTag + ?Sized>(&self) -> Option<Ref<M, T>> {
        Ref::<M, T>::do_static_cast(self)
    }
    /// Casts pointer of this type to reference of given type, returns an error if cast is not possible
    pub fn cast_ref_checked<T : DynamicTypeTag + ?Sized>(&self) -> Ref<M, T> {
        self.cast_ref::<T>().unwrap()
    }
}
