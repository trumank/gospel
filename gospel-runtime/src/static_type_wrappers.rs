use std::ops::{Deref, DerefMut};
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

/// Represents a statically typed wrapper around DynamicPtr with runtime type checking
pub trait TypedDynamicPtrWrapper<M: Memory> where Self: Sized {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self;
    fn get_inner_ptr(&self) -> &DynamicPtr<M>;
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool>;
    fn try_cast(ptr: &DynamicPtr<M>) -> anyhow::Result<Option<Self>> {
        if Self::can_typecast(&ptr.metadata)? { Ok(Some(Self::from_ptr_unchecked(ptr.clone()))) } else { Ok(None) }
    }
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    fn cast<T: TypedDynamicPtrWrapper<M>>(&self) -> anyhow::Result<Option<T>> {
        T::try_cast(self.get_inner_ptr())
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    fn cast_checked<T : TypedDynamicPtrWrapper<M>>(&self) -> anyhow::Result<T> {
        self.cast::<T>()?.ok_or_else(|| anyhow!("Cast failed"))
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    fn add_unchecked(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self::from_ptr_unchecked(self.get_inner_ptr().add_unchecked(count)?))
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    fn sub_unchecked(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self::from_ptr_unchecked(self.get_inner_ptr().sub_unchecked(count)?))
    }
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    fn is_nullptr(&self) -> bool {
        self.get_inner_ptr().is_nullptr()
    }
}
impl<M: Memory> DynamicPtr<M> {
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    pub fn cast<T: TypedDynamicPtrWrapper<M>>(&self) -> anyhow::Result<Option<T>> {
        T::try_cast(self)
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    pub fn cast_checked<T : TypedDynamicPtrWrapper<M>>(&self) -> anyhow::Result<T> {
        self.cast::<T>()?.ok_or_else(|| anyhow!("Cast failed"))
    }
}

/// Implemented for type pointers with statically known types (e.g. pointers to primitive types or complex types composed of primitive types)
pub trait StaticallyTypedPtr<M: Memory> : TypedDynamicPtrWrapper<M> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata>;
    /// Constructs typed pointer from raw pointer and type namespace
    fn from_raw_ptr(ptr: OpaquePtr<M>, namespace: &TypePtrNamespace) -> anyhow::Result<Self> {
        let type_ptr_metadata = Self::store_type_descriptor(namespace)?;
        Ok(Self::from_ptr_unchecked(DynamicPtr{opaque_ptr: ptr, metadata: type_ptr_metadata}))
    }
}

pub trait TrivialValue : Copy + Default {
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool>;
    fn read<M: Memory>(ptr: &TrivialPtr<M, Self>) -> anyhow::Result<Self>;
    fn write<M: Memory>(ptr: &TrivialPtr<M, Self>, value: Self) -> anyhow::Result<()>;
    fn read_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &mut [Self]) -> anyhow::Result<()>;
    fn write_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &[Self]) -> anyhow::Result<()>;
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata>;
}

macro_rules! implement_numeric_trivial_value {
    ( $value_type:ident, $is_integral:literal, $is_floating_point:literal, $primitive_type:expr) => {
       impl TrivialValue for $value_type {
            fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
               if let Some((primitive_type, primitive_size)) = ptr_metadata.primitive_type_and_size()? {
                   Ok(primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<Self>())
               } else { Ok(false) }
            }
            fn read<M: Memory>(ptr: &TrivialPtr<M, Self>) -> anyhow::Result<Self> {
                paste! {
                    ptr.inner_ptr.[<read_ $value_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                }
            }
            fn write<M: Memory>(ptr: &TrivialPtr<M, Self>, value: Self) -> anyhow::Result<()> {
                paste! {
                    ptr.inner_ptr.[<write_ $value_type>](value)
                }
            }
            fn read_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                 paste! {
                    if !ptr.inner_ptr.[<read_ $value_type _slice_unchecked>](buffer)? {
                        Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    } else { Ok({}) }
                }
            }
            fn write_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &[$value_type]) -> anyhow::Result<()> {
                paste! {
                    ptr.inner_ptr.[<write_ $value_type _slice_unchecked>](buffer)
                }
            }
            fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
                let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
                let type_index = type_graph.store_type(Type::Primitive($primitive_type));
                Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
            }
        }
    };
}
implement_numeric_trivial_value!(u8, true, false, PrimitiveType::UnsignedChar);
implement_numeric_trivial_value!(u16, true, false, PrimitiveType::UnsignedShortInt);
implement_numeric_trivial_value!(u32, true, false, PrimitiveType::UnsignedInt);
implement_numeric_trivial_value!(u64, true, false, PrimitiveType::UnsignedLongLongInt);
implement_numeric_trivial_value!(i8, true, false, PrimitiveType::Char);
implement_numeric_trivial_value!(i16, true, false, PrimitiveType::ShortInt);
implement_numeric_trivial_value!(i32, true, false, PrimitiveType::Int);
implement_numeric_trivial_value!(i64, true, false, PrimitiveType::LongLongInt);
implement_numeric_trivial_value!(f32, false, true, PrimitiveType::Float);
implement_numeric_trivial_value!(f64, false, true, PrimitiveType::Double);

macro_rules! implement_variable_size_trivial_value {
    ( $value_type:ident, $large_underlying_type:ident, $small_underlying_type:ident, $primitive_type:expr, $secondary_primitive_type:expr) => {
        paste! {
            impl TrivialValue for $value_type {
                fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
                    if let Some((primitive_type_local_name, _)) = ptr_metadata.primitive_type_and_size()? {
                        Ok(primitive_type_local_name == $primitive_type || primitive_type_local_name == $secondary_primitive_type)
                    } else { Ok(false) }
                }
                fn read<M: Memory>(ptr: &TrivialPtr<M, Self>) -> anyhow::Result<Self> {
                    let (_, primitive_size) = ptr.inner_ptr.metadata.primitive_type_and_size()?
                        .ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))?;
                    if primitive_size == size_of::<$small_underlying_type>() {
                        Ok($value_type(ptr.inner_ptr.[<read_ $small_underlying_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))? as $large_underlying_type))
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        Ok($value_type(ptr.inner_ptr.[<read_ $large_underlying_type>]()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))? as $large_underlying_type))
                    } else {
                        Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn write<M: Memory>(ptr: &TrivialPtr<M, Self>, value: Self) -> anyhow::Result<()> {
                   let (_, primitive_size) = ptr.inner_ptr.metadata.primitive_type_and_size()?
                        .ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))?;
                   if primitive_size == size_of::<$small_underlying_type>() {
                       ptr.inner_ptr.[<write_ $small_underlying_type>](value.0 as $small_underlying_type)
                   } else if primitive_size == size_of::<$large_underlying_type>() {
                       ptr.inner_ptr.[<write_ $large_underlying_type>](value.0 as $large_underlying_type)
                   } else {
                       Err(anyhow!("Failed to write: value is not compatible with {} type", core::stringify!($value_type)))
                   }
                }
                fn read_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                    let (_, primitive_size) = ptr.inner_ptr.metadata.primitive_type_and_size()?
                        .ok_or_else(|| anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))?;
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        if !ptr.inner_ptr.[<read_ $small_underlying_type _slice_unchecked>](local_buffer.deref_mut())? {
                            bail!("Failed to read: value is not compatible with {} type", core::stringify!($value_type));
                        }
                        for index in 0..buffer.len() {
                            buffer[index] = $value_type(local_buffer[index] as $large_underlying_type)
                        }
                        Ok({})
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        if !ptr.inner_ptr.[<read_ $large_underlying_type _slice_unchecked>](local_buffer.deref_mut())? {
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
                fn write_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &[Self]) -> anyhow::Result<()> {
                    let (_, primitive_size) = ptr.inner_ptr.metadata.primitive_type_and_size()?
                        .ok_or_else(|| anyhow!("Failed to write: value is not compatible with {} type", core::stringify!($value_type)))?;
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $small_underlying_type;
                        }
                        ptr.inner_ptr.[<write_ $small_underlying_type _slice_unchecked>](local_buffer.deref())
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $large_underlying_type;
                        }
                        ptr.inner_ptr.[<write_ $large_underlying_type _slice_unchecked>](local_buffer.deref())
                    } else {
                       Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
                    let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
                    let type_index = type_graph.store_type(Type::Primitive($primitive_type));
                    Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
                }
            }
        }
    };
}

implement_variable_size_trivial_value!(LongInt, i64, i32, PrimitiveType::LongInt, PrimitiveType::UnsignedLongInt);
implement_variable_size_trivial_value!(UnsignedLongInt, u64, u32, PrimitiveType::UnsignedLongInt, PrimitiveType::LongInt);
implement_variable_size_trivial_value!(WideChar, u32, u16, PrimitiveType::WideChar, PrimitiveType::WideChar);

impl TrivialValue for bool {
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
        if let Some((primitive_type, _)) = ptr_metadata.primitive_type_and_size()? {
            Ok(primitive_type == PrimitiveType::Bool || primitive_type == PrimitiveType::Char || primitive_type == PrimitiveType::UnsignedChar)
        } else { Ok(false) }
    }
    fn read<M: Memory>(ptr: &TrivialPtr<M, Self>) -> anyhow::Result<Self> {
        Ok(ptr.inner_ptr.read_u8()?.ok_or_else(|| anyhow!("Failed to read: value is not compatible with bool type"))? != 0)
    }
    fn write<M: Memory>(ptr: &TrivialPtr<M, Self>, value: Self) -> anyhow::Result<()> {
        ptr.inner_ptr.write_u8(if value { 1 } else { 0 })
    }
    fn read_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &mut [Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        if !ptr.inner_ptr.read_u8_slice_unchecked(byte_buffer.deref_mut())? {
            bail!("Failed to read: value is not compatible with bool type");
        }
        for index in 0..buffer.len() {
            buffer[index] = byte_buffer[index] != 0;
        }
        Ok({})
    }
    fn write_slice_unchecked<M: Memory>(ptr: &TrivialPtr<M, Self>, buffer: &[Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        for index in 0..buffer.len() {
            byte_buffer[index] = if buffer[index] { 1 } else { 0 };
        }
        ptr.inner_ptr.write_u8_slice_unchecked(byte_buffer.deref())
    }
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
        let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_index = type_graph.store_type(Type::Primitive(PrimitiveType::Bool));
        Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TrivialPtr<M: Memory, T: TrivialValue> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T :TrivialValue> TrivialPtr<M, T> {
    pub fn read(&self) -> anyhow::Result<T> { T::read(self) }
    pub fn write(&self, value: T) -> anyhow::Result<()> { T::write(self, value) }
    pub fn read_slice_unchecked(&self, len: usize) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); len];
        T::read_slice_unchecked(self, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    pub fn write_slice_unchecked(&self, slice: &[T]) -> anyhow::Result<()> {
        T::write_slice_unchecked(self, slice)
    }
}
impl<M: Memory, T : TrivialValue> TypedDynamicPtrWrapper<M> for TrivialPtr<M, T> {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    fn get_inner_ptr(&self) -> &DynamicPtr<M> {
        &self.inner_ptr
    }
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
        T::can_typecast(ptr_metadata)
    }
}
impl<M: Memory, T : TrivialValue> StaticallyTypedPtr<M> for TrivialPtr<M, T> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
        T::store_type_descriptor(namespace)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StaticArrayPtr<M: Memory, T : TypedDynamicPtrWrapper<M>> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> StaticArrayPtr<M, T> {
    pub fn static_len(&self) -> anyhow::Result<usize> {
        self.inner_ptr.metadata.array_static_array_length()?.ok_or_else(|| anyhow!("Ptr does not point to a statically sized array"))
    }
    pub fn element_metadata(&self) -> anyhow::Result<TypePtrMetadata> {
        Ok(self.inner_ptr.metadata.with_type_index(self.inner_ptr.metadata.array_element_type_index()?.ok_or_else(|| anyhow!("Ptr does not point to a statically sized array"))?))
    }
    pub fn element_ptr(&self, index: usize) -> anyhow::Result<T> {
        Ok(T::from_ptr_unchecked(self.inner_ptr.get_array_element_ptr(index)?.ok_or_else(|| anyhow!("Ptr does not point to a statically sized array"))?))
    }
}
impl<M: Memory, T : TrivialValue> StaticArrayPtr<M, TrivialPtr<M, T>> {
    pub fn read_element(&self, index: usize) -> anyhow::Result<T> {
        self.element_ptr(index)?.read()
    }
    pub fn write_element(&self, index: usize, value: T) -> anyhow::Result<()> {
        self.element_ptr(index)?.write(value)
    }
    pub fn read_array(&self) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); self.static_len()?];
        T::read_slice_unchecked(&self.element_ptr(0)?, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    pub fn write_array(&self, array: &[T]) -> anyhow::Result<()> {
        if self.static_len()? != array.len() {
            bail!("Static array length mismatch: Array length is {}, but passed slice len is {}", self.static_len()?, array.len());
        }
        T::write_slice_unchecked(&self.element_ptr(0)?, array)
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M> + StaticallyTypedPtr<M>> StaticArrayPtr<M, T> {
    pub fn from_raw_ptr(ptr: OpaquePtr<M>, namespace: &TypePtrNamespace, array_length: usize) -> anyhow::Result<StaticArrayPtr<M, T>> {
        let type_ptr_metadata = Self::store_type_descriptor(namespace, array_length)?;
        Ok(Self::from_ptr_unchecked(DynamicPtr{opaque_ptr: ptr, metadata: type_ptr_metadata}))
    }
    pub fn store_type_descriptor(namespace: &TypePtrNamespace, array_length: usize) -> anyhow::Result<TypePtrMetadata> {
        let element_type_index = T::store_type_descriptor(namespace)?;
        let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_index = type_graph.store_type(Type::Array(ArrayType{element_type_index: element_type_index.type_index, array_length}));
        Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> TypedDynamicPtrWrapper<M> for StaticArrayPtr<M, T> {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    fn get_inner_ptr(&self) -> &DynamicPtr<M> {
        &self.inner_ptr
    }
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
        if let Some(element_type_index) = ptr_metadata.array_element_type_index()? {
            let element_ptr_metadata = ptr_metadata.with_type_index(element_type_index);
            T::can_typecast(&element_ptr_metadata)
        } else { Ok(false) }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IndirectPtr<M: Memory, T : TypedDynamicPtrWrapper<M>> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> IndirectPtr<M, T> {
    pub fn read(&self) -> anyhow::Result<Option<T>> {
        let result_ptr = self.inner_ptr.read_ptr()?.ok_or_else(|| anyhow!("Ptr does not point to a ptr"))?;
        Ok(result_ptr.map(|x| T::from_ptr_unchecked(x)))
    }
    pub fn write(&self, value: &Option<T>) -> anyhow::Result<()> {
        if let Some(inner_ptr_value) = value {
            self.inner_ptr.write_ptr(inner_ptr_value.get_inner_ptr())
        } else { self.inner_ptr.write_nullptr() }
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> TypedDynamicPtrWrapper<M> for IndirectPtr<M, T> {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    fn get_inner_ptr(&self) -> &DynamicPtr<M> {
        &self.inner_ptr
    }
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
        if let Some((pointee_type_index, is_reference_type)) = ptr_metadata.pointer_pointee_type_index_and_is_reference()? {
            let pointee_ptr_metadata = ptr_metadata.with_type_index(pointee_type_index);
            Ok(!is_reference_type && T::can_typecast(&pointee_ptr_metadata)?)
        } else { Ok(false) }
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M> + StaticallyTypedPtr<M>> StaticallyTypedPtr<M> for IndirectPtr<M, T> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
        let pointee_type = T::store_type_descriptor(namespace)?;
        let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_index = type_graph.store_type(Type::Pointer(PointerType{pointee_type_index: pointee_type.type_index, is_reference: false}));
        Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IndirectRef<M: Memory, T : TypedDynamicPtrWrapper<M>> {
    pub inner_ptr: DynamicPtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> IndirectRef<M, T> {
    pub fn read(&self) -> anyhow::Result<T> {
        let result_ptr = self.inner_ptr.read_ptr()
            ?.ok_or_else(|| anyhow!("Ptr does not point to a ptr"))?
            .ok_or_else(|| anyhow!("Reference type has illegal value of nullptr"))?;
        Ok(T::from_ptr_unchecked(result_ptr))
    }
    pub fn write(&self, value: &T) -> anyhow::Result<()> {
        self.inner_ptr.write_ptr(value.get_inner_ptr())
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M>> TypedDynamicPtrWrapper<M> for IndirectRef<M, T> {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    fn get_inner_ptr(&self) -> &DynamicPtr<M> {
        &self.inner_ptr
    }
    fn can_typecast(ptr_metadata: &TypePtrMetadata) -> anyhow::Result<bool> {
        if let Some((pointee_type_index, is_reference_type)) = ptr_metadata.pointer_pointee_type_index_and_is_reference()? {
            let pointee_ptr_metadata = ptr_metadata.with_type_index(pointee_type_index);
            Ok(is_reference_type && T::can_typecast(&pointee_ptr_metadata)?)
        } else { Ok(false) }
    }
}
impl<M: Memory, T : TypedDynamicPtrWrapper<M> + StaticallyTypedPtr<M>> StaticallyTypedPtr<M> for IndirectRef<M, T> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
        let pointee_type = T::store_type_descriptor(namespace)?;
        let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_index = type_graph.store_type(Type::Pointer(PointerType{pointee_type_index: pointee_type.type_index, is_reference: true}));
        Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VoidPtr<M: Memory> {
    pub inner_ptr: DynamicPtr<M>,
}
impl<M: Memory> VoidPtr<M> {
    pub fn raw_ptr(&self) -> &OpaquePtr<M> {
        &self.inner_ptr.opaque_ptr
    }
}
impl<M: Memory> TypedDynamicPtrWrapper<M> for VoidPtr<M> {
    fn from_ptr_unchecked(ptr: DynamicPtr<M>) -> Self {
        Self{inner_ptr: ptr}
    }
    fn get_inner_ptr(&self) -> &DynamicPtr<M> {
        &self.inner_ptr
    }
    fn can_typecast(_: &TypePtrMetadata) -> anyhow::Result<bool> {
        Ok(true)
    }
}
impl<M: Memory> StaticallyTypedPtr<M> for VoidPtr<M> {
    fn store_type_descriptor(namespace: &TypePtrNamespace) -> anyhow::Result<TypePtrMetadata> {
        let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_index = type_graph.store_type(Type::Primitive(PrimitiveType::Void));
        Ok(TypePtrMetadata{namespace: namespace.clone(), type_index})
    }
}
