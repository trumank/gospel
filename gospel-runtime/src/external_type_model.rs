use crate::core_type_definitions::EnumUnderlyingType;
use crate::core_type_definitions::{implement_enum_underlying_type, implement_primitive_type_tag, IntegralValueTypeTag, StaticTypeLayoutCache, StaticTypeTag};
use crate::external_memory::{Memory, OpaquePtr};
use anyhow::anyhow;
use gospel_typelib::target_triplet::TargetTriplet;
use gospel_typelib::type_model::{ArrayType, IntegerSignedness, MutableTypeGraph, PointerType, PrimitiveType, Type};
use paste::paste;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Add, Deref, DerefMut, Receiver, Sub};
use std::sync::{Mutex, RwLock};

/// Trait to represent a namespace in which types can be defined for a specific target triplet
pub trait TypeNamespace {
    fn type_target_triplet(&self) -> TargetTriplet;
    fn type_graph(&self) -> &RwLock<dyn MutableTypeGraph>;
    fn type_layout_cache(&self) -> &Mutex<StaticTypeLayoutCache>;
}

/// Combines memory and type namespace into a single type that implements both traits
pub struct MemoryAndTypeNamespace<M : Memory, NS : TypeNamespace> {
    pub memory: M,
    pub namespace: NS,
}
impl<M : Memory, NS : TypeNamespace> Memory for MemoryAndTypeNamespace<M, NS> {
    fn target_triplet(&self) -> TargetTriplet {
        self.memory.target_triplet()
    }
    fn read_chunk(&self, address: u64, buffer: &mut [u8]) -> anyhow::Result<()> {
        self.memory.read_chunk(address, buffer)
    }
    fn write_chunk(&self, address: u64, buffer: &[u8]) -> anyhow::Result<()> {
        self.memory.write_chunk(address, buffer)
    }
}
impl<M : Memory, NS : TypeNamespace> TypeNamespace for MemoryAndTypeNamespace<M, NS> {
    fn type_target_triplet(&self) -> TargetTriplet {
        self.namespace.type_target_triplet()
    }
    fn type_graph(&self) -> &RwLock<dyn MutableTypeGraph> {
        self.namespace.type_graph()
    }
    fn type_layout_cache(&self) -> &Mutex<StaticTypeLayoutCache> {
        self.namespace.type_layout_cache()
    }
}

/// Type large enough to hold any value of type "long int" on any target triplet.
/// Long int can have a size of either 4 or 8 bytes depending on the target triplet
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExternalLongInt(i64);

/// Type large enough to hold any value of type "unsigned long int" on any target triplet.
/// Unsigned long int can have a size of either 4 or 8 bytes depending on the target triplet
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExternalUnsignedLongInt(u64);

/// Type large enough to hold any value of type "wchar_t" on any target triplet.
/// Long int can have a size of either 2 or 4 bytes depending on the target triplet
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExternalWideChar(u32);

// Implement type tags for the external representations of variable-length types
implement_primitive_type_tag!(ExternalLongInt, PrimitiveType::LongInt);
implement_primitive_type_tag!(ExternalUnsignedLongInt, PrimitiveType::UnsignedLongInt);
implement_primitive_type_tag!(ExternalWideChar, PrimitiveType::WideChar);

implement_enum_underlying_type!(ExternalUnsignedLongInt, u64);
implement_enum_underlying_type!(ExternalLongInt, i64);
implement_enum_underlying_type!(ExternalWideChar, u32);

/// Represents a non-null pointer to a value of static type T. This is similar to NonNull<T> type in standard library,
/// but refers to memory that might not be mapped to the process address space or belong to a different target
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Ref<M : Memory + TypeNamespace, T : StaticTypeTag> {
    pub inner_ptr: OpaquePtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory + TypeNamespace, T : StaticTypeTag> Ref<M, T> {
    /// Constructs a ptr from raw ptr. Will panic if provided ptr is null
    pub fn from_raw_ptr(ptr: OpaquePtr<M>) -> Self {
        assert!(!ptr.is_nullptr(), "Attempt to construct Ref from nullptr");
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    /// Casts reference of this type to reference of another type, returns None if cast is not possible
    pub fn cast<R : StaticTypeTag>(&self) -> Option<Ref<M, R>> {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        Ref::<M, R>::do_static_cast(&self.inner_ptr, static_type_index)
    }
    /// Casts pointer of this type to reference of another type, returns an error if cast is not possible
    pub fn cast_checked<R : StaticTypeTag>(&self) -> Ref<M, R> {
        self.cast::<R>().unwrap()
    }
    /// Offsets this reference towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().add(offset_bytes))
    }
    /// Offsets this reference towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().sub(offset_bytes))
    }
    /// Converts this reference to a pointer
    pub fn to_ptr(&self) -> Ptr<M, T> {
        Ptr::from_raw_ptr(self.inner_ptr.clone())
    }
    /// Converts this reference to a dyn pointer with the same type
    pub fn to_dyn_ptr(self) -> DynPtr<M> {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        DynPtr::from_raw_ptr(self.inner_ptr, static_type_index)
    }
    /// Returns the size and alignment of the pointed to static type
    pub fn pointee_size_and_alignment(&self) -> (usize, usize) {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        let mut type_layout_cache = self.inner_ptr.memory.type_layout_cache().lock().unwrap();
        type_layout_cache.get_type_size_and_alignment_cached(self.inner_ptr.memory.type_graph(), static_type_index)
    }
    /// Attempts to cast the given pointer to this reference type. Will return None if types are unrelated or provided ptr points to null
    fn do_static_cast(ptr: &OpaquePtr<M>, from_type_index: usize) -> Option<Self> {
        if let Some(ptr) = Ptr::<M, T>::do_static_cast(ptr, from_type_index) && !ptr.is_nullptr() {
            Some(Self::from_raw_ptr(ptr.inner_ptr))
        } else { None }
    }
}
// Manual implementation required because Rust does not work correctly and puts wrong bounds on derive(Clone)
// See: https://github.com/rust-lang/rust/issues/26925
impl<M : Memory + TypeNamespace, T : StaticTypeTag> Clone for Ref<M, T> {
    fn clone(&self) -> Self {
        Self::from_raw_ptr(self.inner_ptr.clone())
    }
}
impl<M : Memory + TypeNamespace, T : StaticTypeTag> Receiver for Ref<M, T> {
    type Target = T;
}
impl<M : Memory + TypeNamespace, T : StaticTypeTag> StaticTypeTag for Ref<M, T> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: true}))
    }
}

/// Additional functions available on references to externally convertible values
impl<M : Memory + TypeNamespace, T : StaticTypeTag + ExternallyConvertible> Ref<M, T> {
    /// Reads the trivial value from the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<T> {
        T::read_external(&self.inner_ptr)
    }
    /// Writes the trivial value to the memory location pointed to by this reference
    pub fn write(&self, value: T) -> anyhow::Result<()> {
        T::write_external(&self.inner_ptr, value)
    }
    /// Reads the slice of trivial values from the memory location pointed to by this reference
    pub fn read_slice_unchecked(&self, len: usize) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); len];
        T::read_external_slice(&self.inner_ptr, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    /// Writes the slice of trivial values to the memory location pointed to by this reference
    pub fn write_slice_unchecked(&self, slice: &[T]) -> anyhow::Result<()> {
        T::write_external_slice(&self.inner_ptr, slice)
    }
}

/// Additional functions available on references to pointers and references
impl<M : Memory + TypeNamespace, T : StaticTypeTag> Ref<M, Ptr<M, T>> {
    /// Reads the pointer value at the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<Ptr<M, T>> {
        let result_ptr = self.inner_ptr.read_ptr()?;
        Ok(Ptr::from_raw_ptr(result_ptr))
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
impl<M : Memory + TypeNamespace, T : StaticTypeTag> Ref<M, Ref<M, T>> {
    /// Reads the reference value at the memory location pointed to by this reference
    pub fn read(&self) -> anyhow::Result<Ref<M, T>> {
        let result_ptr = self.inner_ptr.read_ptr()?;
        Ok(Ref::from_raw_ptr(result_ptr))
    }
    /// Writes the reference value to the memory location pointed to by this reference
    pub fn write(&self, value: &Ref<M, T>) -> anyhow::Result<()> {
        self.inner_ptr.write_ptr(&value.inner_ptr)
    }
}

/// Represents a pointer to a value of static type T. Can be null
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ptr<M : Memory + TypeNamespace, T : StaticTypeTag> {
    pub inner_ptr: OpaquePtr<M>,
    pub phantom_data: PhantomData<T>,
}
impl<M: Memory + TypeNamespace, T : StaticTypeTag> Ptr<M, T> {
    /// Constructs a ptr from dynamic ptr without checking for the requirements for the successful cast
    pub fn from_raw_ptr(ptr: OpaquePtr<M>) -> Self {
        Self{inner_ptr: ptr, phantom_data: PhantomData::default()}
    }
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    pub fn cast<R : StaticTypeTag>(&self) -> Option<Ptr<M, R>> {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        Ptr::<M, R>::do_static_cast(&self.inner_ptr, static_type_index)
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    pub fn cast_checked<R : StaticTypeTag>(&self) -> Ptr<M, R> {
        self.cast::<R>().unwrap()
    }
    /// Casts pointer of this type to reference of given type, returns None if cast is not possible
    pub fn cast_ref<R: StaticTypeTag>(&self) -> Option<Ref<M, R>> {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        Ref::<M, R>::do_static_cast(&self.inner_ptr, static_type_index)
    }
    /// Casts pointer of this type to reference of given type, returns an error if cast is not possible
    pub fn cast_ref_checked<R : StaticTypeTag>(&self) -> Ref<M, R> {
        self.cast_ref::<R>().unwrap()
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().add(offset_bytes))
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().sub(offset_bytes))
    }
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    pub fn is_nullptr(&self) -> bool {
        self.inner_ptr.is_nullptr()
    }
    /// Converts this pointer to a reference. Returns None if the pointer has the value of null
    pub fn to_ref(self) -> Option<Ref<M, T>> {
        if !self.is_nullptr() { Some(Ref::from_raw_ptr(self.inner_ptr)) } else { None }
    }
    /// Converts this pointer to a reference. Panics if the pointer is null
    pub fn to_ref_checked(self) -> Ref<M, T> {
        self.to_ref().unwrap()
    }
    /// Converts this pointer to a dyn pointer with the same type
    pub fn to_dyn_ptr(self) -> DynPtr<M> {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        DynPtr::from_raw_ptr(self.inner_ptr, static_type_index)
    }
    /// Returns the size and alignment of the pointed to static type
    pub fn pointee_size_and_alignment(&self) -> (usize, usize) {
        let static_type_index = T::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
        let mut type_layout_cache = self.inner_ptr.memory.type_layout_cache().lock().unwrap();
        type_layout_cache.get_type_size_and_alignment_cached(self.inner_ptr.memory.type_graph(), static_type_index)
    }
    /// Attempts to cast the given dynamic pointer to this pointer type. Will return None if types are unrelated
    fn do_static_cast(ptr: &OpaquePtr<M>, from_type_index: usize) -> Option<Self> {
        let to_type_index = T::store_type_descriptor_to_namespace(ptr.memory.deref());
        let adjust_bytes = ptr.memory.type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(&ptr.memory.type_graph(), from_type_index, to_type_index)?;
        Some(Self::from_raw_ptr(ptr.clone().add(adjust_bytes)))
    }
}
// Manual implementation required because Rust does not work correctly and puts wrong bounds on derive(Clone)
// See: https://github.com/rust-lang/rust/issues/26925
impl<M : Memory + TypeNamespace, T : StaticTypeTag> Clone for Ptr<M, T> {
    fn clone(&self) -> Self {
        Self::from_raw_ptr(self.inner_ptr.clone())
    }
}
impl<M : Memory + TypeNamespace, T : StaticTypeTag> StaticTypeTag for Ptr<M, T> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: false}))
    }
}

/// References can be freely converted to pointers
impl<M : Memory + TypeNamespace, T : StaticTypeTag> From<Ref<M, T>> for Ptr<M, T> {
    fn from(value: Ref<M, T>) -> Self {
        value.to_ptr()
    }
}
/// Pointers can be converted to references if they are not null
impl<M : Memory + TypeNamespace, T : StaticTypeTag> TryFrom<Ptr<M, T>> for Ref<M, T> {
    type Error = ();
    fn try_from(value: Ptr<M, T>) -> Result<Self, Self::Error> {
        value.to_ref().ok_or(())
    }
}

/// Represents a statically sized C or C++ array, which is a linear sequence of values of type T
pub struct StaticArray<T : StaticTypeTag, N: IntegralValueTypeTag> {
    phantom_data_element_type: PhantomData<T>,
    phantom_data_array_count: PhantomData<N>,
}
impl<T : StaticTypeTag, N: IntegralValueTypeTag> StaticArray<T, N> {
    /// Returns the length of this statically sized array
    pub fn static_len() -> usize {
        N::get_raw_integral_value() as usize
    }
    /// Returns the pointer to the first element of the array
    pub fn base_ref<M : Memory + TypeNamespace>(self: &Ref<M, Self>) -> Ref<M, T> {
        Ref::<M, T>::from_raw_ptr(self.inner_ptr.clone())
    }
    /// Returns the pointer to the array element at index. Will panic if index is out of bounds
    pub fn element_ref<M : Memory + TypeNamespace>(self: &Ref<M, Self>, index: usize) -> Ref<M, T> {
        assert!(index < Self::static_len());
        Self::base_ref(self).add_unchecked(index)
    }
}
impl<T : StaticTypeTag, N: IntegralValueTypeTag> StaticTypeTag for StaticArray<T, N> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let element_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let array_length = N::get_raw_integral_value() as usize;
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Array(ArrayType{element_type_index, array_length}))
    }
}

/// Additional functions available on arrays of externally convertible values
impl<T : StaticTypeTag + ExternallyConvertible, N: IntegralValueTypeTag> StaticArray<T, N> {
    /// Reads the static array element value from memory location at given index
    pub fn read_element<M : Memory + TypeNamespace>(self: &Ref<M, Self>, index: usize) -> anyhow::Result<T> {
        Self::element_ref(self, index).read()
    }
    /// Writes to the static array element memory location at given index
    pub fn write_element<M : Memory + TypeNamespace>(self: &Ref<M, Self>, index: usize, value: T) -> anyhow::Result<()> {
        Self::element_ref(self, index).write(value)
    }
    /// Reads contents of the entire statically sized array into a vector
    pub fn read_array<M : Memory + TypeNamespace>(self: &Ref<M, Self>) -> anyhow::Result<Vec<T>> {
        let mut result_buffer = vec![T::default(); Self::static_len()];
        T::read_external_slice(&self.inner_ptr, result_buffer.as_mut_slice())?;
        Ok(result_buffer)
    }
    /// Writes contents of the entire statically sized array from a slice
    pub fn write_array<M : Memory + TypeNamespace>(self: &Ref<M, Self>, array: &[T]) -> anyhow::Result<()> {
        assert_eq!(Self::static_len(), array.len(), "Static array length mismatch: Array length is {}, but passed slice len is {}", Self::static_len(), array.len());
        T::write_external_slice(&self.inner_ptr, array)
    }
}

/// Trait implemented by values that can be copied from and to the external memory to the local memory
/// Values might need to be converted to be of a compatible type, e.g. endian flip or ptr coercion or extension/truncation might be necessary
pub trait ExternallyConvertible : Default + Clone {
    fn read_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>) -> anyhow::Result<Self>;
    fn write_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, value: Self) -> anyhow::Result<()>;
    fn read_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()>;
    fn write_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()>;
}

macro_rules! implement_externally_convertible_for_primitive_type {
    ($value_type:ident) => {
       impl ExternallyConvertible for $value_type {
            fn read_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>) -> anyhow::Result<Self> {
                paste! {
                    ptr.[<read_ $value_type>]()
                }
            }
            fn write_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                paste! {
                    ptr.[<write_ $value_type>](value)
                }
            }
            fn read_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                 paste! {
                    ptr.[<read_ $value_type _array>](buffer)
                }
            }
            fn write_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &[$value_type]) -> anyhow::Result<()> {
                paste! {
                    ptr.[<write_ $value_type _array>](buffer)
                }
            }
        }
    };
}

// Implement externally convertible trait for primitive types
implement_externally_convertible_for_primitive_type!(u8);
implement_externally_convertible_for_primitive_type!(u16);
implement_externally_convertible_for_primitive_type!(u32);
implement_externally_convertible_for_primitive_type!(u64);
implement_externally_convertible_for_primitive_type!(i8);
implement_externally_convertible_for_primitive_type!(i16);
implement_externally_convertible_for_primitive_type!(i32);
implement_externally_convertible_for_primitive_type!(i64);
implement_externally_convertible_for_primitive_type!(f32);
implement_externally_convertible_for_primitive_type!(f64);

macro_rules! implement_variable_size_trivial_value {
    ( $value_type:ident, $large_underlying_type:ident, $small_underlying_type:ident, $primitive_type:expr) => {
        paste! {
            impl ExternallyConvertible for $value_type {
                fn read_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>) -> anyhow::Result<Self> {
                    let target_triplet = ptr.memory.target_triplet();
                    let primitive_size = $primitive_type.bit_width(&target_triplet).unwrap().value_in_bytes();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        Ok($value_type(ptr.[<read_ $small_underlying_type>]()? as $large_underlying_type))
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        Ok($value_type(ptr.[<read_ $large_underlying_type>]()? as $large_underlying_type))
                    } else {
                        Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn write_external<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                    let target_triplet = ptr.memory.target_triplet();
                    let primitive_size = $primitive_type.bit_width(&target_triplet).unwrap().value_in_bytes();
                   if primitive_size == size_of::<$small_underlying_type>() {
                       ptr.[<write_ $small_underlying_type>](value.0 as $small_underlying_type)
                   } else if primitive_size == size_of::<$large_underlying_type>() {
                       ptr.[<write_ $large_underlying_type>](value.0 as $large_underlying_type)
                   } else {
                       Err(anyhow!("Failed to write: value is not compatible with {} type", core::stringify!($value_type)))
                   }
                }
                fn read_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &mut [$value_type]) -> anyhow::Result<()> {
                    let target_triplet = ptr.memory.target_triplet();
                    let primitive_size = $primitive_type.bit_width(&target_triplet).unwrap().value_in_bytes();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        ptr.[<read_ $small_underlying_type _array>](local_buffer.deref_mut())?;
                        for index in 0..buffer.len() {
                            buffer[index] = $value_type(local_buffer[index] as $large_underlying_type)
                        }
                        Ok({})
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        ptr.[<read_ $large_underlying_type _array>](local_buffer.deref_mut())?;
                        for index in 0..buffer.len() {
                            buffer[index] = $value_type(local_buffer[index] as $large_underlying_type)
                        }
                        Ok({})
                    } else {
                       Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
                fn write_external_slice<M: Memory + TypeNamespace>(ptr: &OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                    let target_triplet = ptr.memory.target_triplet();
                    let primitive_size = $primitive_type.bit_width(&target_triplet).unwrap().value_in_bytes();
                    if primitive_size == size_of::<$small_underlying_type>() {
                        let mut local_buffer: Box<[$small_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $small_underlying_type;
                        }
                        ptr.[<write_ $small_underlying_type _array>](local_buffer.deref())
                    } else if primitive_size == size_of::<$large_underlying_type>() {
                        let mut local_buffer: Box<[$large_underlying_type]> = vec![0; buffer.len()].into_boxed_slice();
                        for index in 0..buffer.len() {
                            local_buffer[index] = buffer[index].0 as $large_underlying_type;
                        }
                        ptr.[<write_ $large_underlying_type _array>](local_buffer.deref())
                    } else {
                       Err(anyhow!("Failed to read: value is not compatible with {} type", core::stringify!($value_type)))
                    }
                }
            }
        }
    };
}
implement_variable_size_trivial_value!(ExternalLongInt, i64, i32, PrimitiveType::LongInt);
implement_variable_size_trivial_value!(ExternalUnsignedLongInt, u64, u32, PrimitiveType::UnsignedLongInt);
implement_variable_size_trivial_value!(ExternalWideChar, u32, u16, PrimitiveType::WideChar);

impl ExternallyConvertible for bool {
    fn read_external<M: Memory>(ptr: &OpaquePtr<M>) -> anyhow::Result<Self> {
        Ok(ptr.read_u8()? != 0)
    }
    fn write_external<M: Memory>(ptr: &OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
        ptr.write_u8(if value { 1 } else { 0 })
    }
    fn read_external_slice<M: Memory>(ptr: &OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        ptr.read_u8_array(byte_buffer.deref_mut())?;
        for index in 0..buffer.len() {
            buffer[index] = byte_buffer[index] != 0;
        }
        Ok({})
    }
    fn write_external_slice<M: Memory>(ptr: &OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
        let mut byte_buffer: Box<[u8]> = vec![0; buffer.len()].into_boxed_slice();
        for index in 0..buffer.len() {
            byte_buffer[index] = if buffer[index] { 1 } else { 0 };
        }
        ptr.write_u8_array(byte_buffer.deref())
    }
}

/// Represents a pointer without a statically known type. It can be cast to a statically typed ptr using cast functions,
/// and some type-agnostic operations can be performed on it using the type index stored
#[derive(Clone, PartialEq, Eq)]
pub struct DynPtr<M: Memory + TypeNamespace> {
    pub inner_ptr: OpaquePtr<M>,
    pub type_index: usize,
}
impl<M: Memory + TypeNamespace> DynPtr<M> {
    /// Constructs a ptr from a pointer and type index
    pub fn from_raw_ptr(ptr: OpaquePtr<M>, type_index: usize) -> Self {
        Self{inner_ptr: ptr, type_index}
    }
    /// Casts pointer of this type to pointer of another type, returns None if cast is not possible
    pub fn cast<R : StaticTypeTag>(&self) -> Option<Ptr<M, R>> {
        Ptr::<M, R>::do_static_cast(&self.inner_ptr, self.type_index)
    }
    /// Casts pointer of this type to pointer of another type, returns an error if cast is not possible
    pub fn cast_checked<R : StaticTypeTag>(&self) -> Ptr<M, R> {
        self.cast::<R>().unwrap()
    }
    /// Casts pointer of this type to reference of given type, returns None if cast is not possible
    pub fn cast_ref<R: StaticTypeTag>(&self) -> Option<Ref<M, R>> {
        Ref::<M, R>::do_static_cast(&self.inner_ptr, self.type_index)
    }
    /// Casts pointer of this type to reference of given type, returns an error if cast is not possible
    pub fn cast_ref_checked<R : StaticTypeTag>(&self) -> Ref<M, R> {
        self.cast_ref::<R>().unwrap()
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().add(offset_bytes), self.type_index)
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        let offset_bytes = self.pointee_size_and_alignment().0 * count;
        Self::from_raw_ptr(self.inner_ptr.clone().sub(offset_bytes), self.type_index)
    }
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    pub fn is_nullptr(&self) -> bool {
        self.inner_ptr.is_nullptr()
    }
    /// Returns the pointer to the array element at the given index. Performs boundaries check
    pub fn get_array_element_ptr(&self, array_element_index: usize) -> Option<Self> {
        if let Some(static_array_length) = self.array_static_array_length() && array_element_index < static_array_length {
            Some(self.add_unchecked(array_element_index))
        } else { None }
    }
    /// Returns the pointer to the struct field with the given name
    pub fn get_struct_field_ptr(&self, field_name: &str) -> Option<Self> {
        if let Some((field_type_index, field_offset)) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset(self.inner_ptr.memory.type_graph(), self.type_index, field_name) {
            Some(Self::from_raw_ptr(self.inner_ptr.clone().add(field_offset), field_type_index))
        } else { None }
    }
    /// Returns the pointer to the struct field with the given name. Caches the result by string ptr
    pub fn get_struct_field_ptr_cached(&self, field_name: &'static str) -> Option<Self> {
        if let Some((field_type_index, field_offset)) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(self.inner_ptr.memory.type_graph(), self.type_index, field_name) {
            Some(Self::from_raw_ptr(self.inner_ptr.clone().add(field_offset), field_type_index))
        } else { None }
    }
    /// Reads value of this pointer as a value of integral type. Value will be zero-extended (for unsigned values) or sign-extended (for signed values) to 64 bit
    pub fn read_integral_type(&self) -> anyhow::Result<u64> {
        if let Some((primitive_type, primitive_size)) = self.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_type.integer_signedness().unwrap() {
                IntegerSignedness::Signed => {
                    match primitive_size {
                        1 => Ok(self.inner_ptr.read_i8()? as u64),
                        2 => Ok(self.inner_ptr.read_i16()? as u64),
                        4 => Ok(self.inner_ptr.read_i32()? as u64),
                        8 => Ok(self.inner_ptr.read_i64()? as u64),
                        _ => Err(anyhow!("unknown integral primitive size"))
                    }
                }
                IntegerSignedness::Unsigned => {
                    match primitive_size {
                        1 => Ok(self.inner_ptr.read_u8()? as u64),
                        2 => Ok(self.inner_ptr.read_u16()? as u64),
                        4 => Ok(self.inner_ptr.read_u32()? as u64),
                        8 => Ok(self.inner_ptr.read_u64()?),
                        _ => Err(anyhow!("unknown integral primitive size"))
                    }
                }
            }
        } else { Err(anyhow!("Not an integral type")) }
    }
    /// Reads value of this pointer as a value of integral type. Values will be zero-extended (for unsigned values) or sign-extended (for signed values) to 64 bit
    pub fn read_integral_type_slice(&self, buffer: &mut [u64]) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_type.integer_signedness().unwrap() {
                IntegerSignedness::Signed => {
                    match primitive_size {
                        1 => {
                            let mut underlying_buffer: Box<[i8]> = vec![0i8; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_i8_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        2 => {
                            let mut underlying_buffer: Box<[i16]> = vec![0i16; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_i16_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        4 => {
                            let mut underlying_buffer: Box<[i32]> = vec![0i32; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_i32_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        8 => {
                            self.inner_ptr.read_u64_array(buffer)
                        },
                        _ => Err(anyhow!("unknown integral primitive size"))
                    }
                }
                IntegerSignedness::Unsigned => {
                    match primitive_size {
                        1 => {
                            let mut underlying_buffer: Box<[u8]> = vec![0u8; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_u8_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        2 => {
                            let mut underlying_buffer: Box<[u16]> = vec![0u16; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_u16_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        4 => {
                            let mut underlying_buffer: Box<[u32]> = vec![0u32; buffer.len()].into_boxed_slice();
                            self.inner_ptr.read_u32_array(underlying_buffer.deref_mut())?;
                            for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                            Ok({})
                        },
                        8 => {
                            self.inner_ptr.read_u64_array(buffer)
                        },
                        _ => Err(anyhow!("unknown integral primitive size"))
                    }
                }
            }
        } else { Err(anyhow!("Not an integral type")) }
    }
    /// Writes value of this pointer as a value of integral type. Unused bits will be discarded
    pub fn write_integral_type(&self, value: u64) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => self.inner_ptr.write_u8(value as u8),
                2 => self.inner_ptr.write_u16(value as u16),
                4 => self.inner_ptr.write_u32(value as u32),
                8 => self.inner_ptr.write_u64(value),
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Err(anyhow!("Not an integral type")) }
    }
    /// Writes value of this pointer as a value of integral type. Unused bits will be discarded
    pub fn write_integral_type_slice(&self, buffer: &[u64]) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => {
                    let mut underlying_buffer: Box<[u8]> = vec![0u8; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u8; }
                    self.inner_ptr.write_u8_array(underlying_buffer.deref())?;
                    Ok({})
                },
                2 => {
                    let mut underlying_buffer: Box<[u16]> = vec![0u16; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u16; }
                    self.inner_ptr.write_u16_array(underlying_buffer.deref())?;
                    Ok({})
                },
                4 => {
                    let mut underlying_buffer: Box<[u32]> = vec![0u32; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u32; }
                    self.inner_ptr.write_u32_array(underlying_buffer.deref())?;
                    Ok({})
                },
                8 => {
                    self.inner_ptr.write_u64_array(buffer)?;
                    Ok({})
                },
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Err(anyhow!("Not an integral type")) }
    }
    /// Returns the size and alignment of the pointed to static type
    pub fn pointee_size_and_alignment(&self) -> (usize, usize) {
        let mut type_layout_cache = self.inner_ptr.memory.type_layout_cache().lock().unwrap();
        type_layout_cache.get_type_size_and_alignment_cached(self.inner_ptr.memory.type_graph(), self.type_index)
    }
    /// Returns the type index of the array element if this pointer represents a statically sized array
    pub fn array_element_type_index(&self) -> Option<usize> {
        let type_graph = self.inner_ptr.memory.type_graph().read().unwrap();
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Some(array_type.element_type_index)
        } else { None }
    }
    /// Returns the length of the statically sized array if this pointer represents a statically sized array
    pub fn array_static_array_length(&self) -> Option<usize> {
        let type_graph = self.inner_ptr.memory.type_graph().read().unwrap();
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Some(array_type.array_length)
        } else { None }
    }
    /// Returns name of the struct if this pointer represents an UDT
    pub fn struct_type_name(&self) -> Option<String> {
        let type_graph = self.inner_ptr.memory.type_graph().read().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.name.clone()
        } else { None }
    }
    /// Returns primitive type and its size if this pointer represents a primitive type
    pub fn primitive_type_and_size(&self) -> Option<(PrimitiveType, usize)> {
        let type_graph = self.inner_ptr.memory.type_graph().read().unwrap();
        let target_triplet = self.inner_ptr.memory.target_triplet();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Primitive(primitive_type) = type_data {
            Some((primitive_type.clone(), primitive_type.size_and_alignment(&target_triplet).unwrap()))
        } else if let Type::Enum(enum_type) = type_data {
            let underlying_primitive_type = enum_type.underlying_type(&target_triplet).unwrap();
            Some((underlying_primitive_type, underlying_primitive_type.size_and_alignment(&target_triplet).unwrap()))
        } else { None }
    }
    pub fn struct_find_all_base_classes_by_type_name(&self, full_base_class_type_name: &str) -> Option<Vec<usize>> {
        let type_graph = self.inner_ptr.memory.type_graph().read().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            let all_distinct_base_classes: BTreeSet<usize> = user_defined_type.base_class_recursive_iterator(type_graph.deref()).collect();
            let matching_base_classes: Vec<usize> = all_distinct_base_classes.into_iter()
                .filter(|base_class_index| {
                    if let Type::UDT(base_class_type) = type_graph.type_by_index(*base_class_index) {
                        base_class_type.name.as_ref().map(|x| x.as_str()) == Some(full_base_class_type_name)
                    } else { false }
                }).collect();
            Some(matching_base_classes)
        } else { None }
    }
}
