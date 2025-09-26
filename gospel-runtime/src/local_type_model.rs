use std::alloc::{Allocator, Layout};
use std::marker::{PhantomData};
use std::ops::{Deref, DerefMut};
use std::{mem, ptr};
use std::ptr::{NonNull, Pointee};
use std::sync::{Mutex, RwLock};
use gospel_typelib::compiled_target_triplet;
use gospel_typelib::target_triplet::TargetTriplet;
use gospel_typelib::type_model::{MutableTypeGraph, PrimitiveType, Type};
use crate::core_type_definitions::{implement_primitive_type_tag, StaticTypeLayoutCache, StaticTypeTag};

// Underlying type definitions for long int, unsigned long int and wide char depending on target platform
#[cfg(platform_long_size="4")]
pub type PlatformLongIntUnderlyingType = i32;
#[cfg(platform_long_size="8")]
pub type PlatformLongIntUnderlyingType = i64;

#[cfg(platform_long_size="4")]
pub type PlatformUnsignedLongIntUnderlyingType = u32;
#[cfg(platform_long_size="8")]
pub type PlatformUnsignedLongIntUnderlyingType = u64;

#[cfg(platform_wide_char_size="2")]
pub type PlatformWideCharUnderlyingType = u16;
#[cfg(platform_wide_char_size="4")]
pub type PlatformWideCharUnderlyingType = u32;

/// Represents a long int type with the bit width native to the running platform. Size can be either 4 or 8 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PlatformLongInt(PlatformLongIntUnderlyingType);

/// Represents an unsigned long int type with the bit width native to the running platform. Size can be either 4 or 8 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
#[cfg(platform_long_size="4")]
pub struct PlatformUnsignedLongInt(PlatformUnsignedLongIntUnderlyingType);

/// Represents a wide character type with the bit width native to the running platform. Size can be either 2 or 4 depending on the platform
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PlatformWideChar(PlatformWideCharUnderlyingType);

implement_primitive_type_tag!(PlatformLongInt, PrimitiveType::LongInt);
implement_primitive_type_tag!(PlatformUnsignedLongInt, PrimitiveType::UnsignedLongInt);
implement_primitive_type_tag!(PlatformWideChar, PrimitiveType::WideChar);

/// Returns the target triplet for which this module has been compiled
pub fn native_target_triplet() -> TargetTriplet {
    compiled_target_triplet().unwrap()
}

/// Type universe represents a contained type graph
pub trait TypeUniverse {
    fn target_triplet() -> TargetTriplet;
    fn type_graph() -> &'static RwLock<dyn MutableTypeGraph>;
    fn type_layout_cache() -> &'static Mutex<StaticTypeLayoutCache>;
}

/// Represents a mutable C++ reference (a non-null value pointer)
/// C++ References do not follow Rust reference semantics, and allow arbitrary mutation as well as sharing read and write access arbitrarily
/// C++ references implement Deref and DerefMut and can be temporarily converted to Rust references (immutable or otherwise)
/// This type transparently wraps a non-null byte pointer. Note that this implies that the pointer must be a thin pointer
/// Wide pointers are only supported if metadata can be derived statically from the value of the pointer as raw sequence of bytes
///
/// It is users responsibility to ensure that Rust reference semantics are followed when Deref and DerefMut are used. In general, avoid holding on to Rust references
/// and only use them to read/modify pointed value and/or call C++ functions on them. In all other cases, like storing the value in complex types,
/// prefer storing CRef value directly instead of storing a reference to ensure that Rust reference semantics are not violated
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct CRef<T : ?Sized> {
    raw_ptr: NonNull<()>,
    phantom_data: PhantomData<T>,
}
impl<T : ?Sized> CRef<T> {
    /// Creates a reference from a raw pointer. Will panic if the pointer is null
    pub fn from_raw_ptr(ptr: *const T) -> Self {
        Self{raw_ptr: NonNull::new(ptr as *mut ()).unwrap(), phantom_data: PhantomData::default()}
    }
}

/// Implement this on DSTs that can have their metadata implicitly derived
pub trait ImplicitPtrMetadata : Pointee {
    /// Returns the metadata that can be implicitly created to determine the size of the value of this type
    /// Since ImplicitPtrMetadata can only be implemented for user-defined DSTs backed by a slice, this function should return the statically known size of the backing slice
    fn create_implicit_metadata() -> Self::Metadata;
    /// Returns the size of the value of this type, in bytes, using the implicit metadata
    fn static_size_of_val() -> usize {
        let null_ptr_with_metadata = ptr::from_raw_parts::<Self>(ptr::null::<()>(), Self::create_implicit_metadata());
        unsafe { mem::size_of_val_raw(null_ptr_with_metadata) }
    }
    /// Returns the alignment requirements for the value of this type, in bytes. Default implementation just uses align_of_val_raw, which might be incorrect if higher alignment is required
    fn static_align_of_val() -> usize {
        let null_ptr_with_metadata = ptr::from_raw_parts::<Self>(ptr::null::<()>(), Self::create_implicit_metadata());
        unsafe { mem::align_of_val_raw(null_ptr_with_metadata) }
    }
}
/// Default specialization for statically sized types which have no pointer metadata
impl<T : Pointee<Metadata = ()>> ImplicitPtrMetadata for T {
    fn create_implicit_metadata() -> Self::Metadata { () }
}

/// C references can be converted to wide pointers for DSTs with statically known (implicit) metadata
impl<T : ?Sized + ImplicitPtrMetadata> CRef<T> {
    /// Converts this C reference to a raw pointer to the underlying value
    pub fn as_ptr(&self) -> *const T {
        ptr::from_raw_parts::<T>(self.raw_ptr.as_ptr(), T::create_implicit_metadata())
    }
    /// Converts this C reference to a raw pointer to the underlying value
    pub fn as_mut_ptr(&mut self) -> *mut T {
        ptr::from_raw_parts_mut::<T>(self.raw_ptr.as_ptr(), T::create_implicit_metadata())
    }
}

/// Implementation of Deref for references to implicitly sized dynamically sized types
impl<T: ?Sized + ImplicitPtrMetadata> Deref for CRef<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.as_ptr().as_ref().unwrap() }
    }
}
/// Implementation of DerefMut for references to implicitly sized dynamically sized types
impl<T : ?Sized + ImplicitPtrMetadata> DerefMut for CRef<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.as_mut_ptr().as_mut().unwrap() }
    }
}


/// Direct access functions implemented for bitwise copyable types
impl<T : Copy> CRef<T> {
    /// Performs a bitwise copy of the given value from the pointer
    pub fn read(&self) -> T {
        unsafe { ptr::read(self.as_ptr()) }
    }
    /// Writes a bitwise copy of the given value to the pointer
    pub fn write(&mut self, value: T) {
        unsafe { ptr::write(self.as_mut_ptr(), value) }
    }
}

/// Allocates a slice of memory using the size and alignment requirements of the given type
pub fn allocate_uninitialized<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: A) -> NonNull<T> {
    let raw_ptr = alloc.allocate(Layout::from_size_align(T::static_size_of_val(), T::static_align_of_val()).unwrap()).unwrap().as_ptr() as *mut u8;
    NonNull::new(ptr::from_raw_parts_mut(raw_ptr, T::create_implicit_metadata())).unwrap()
}

/// Allocates a slice of memory using the size and alignment requirements of the given type
pub fn allocate_zeroed<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: A) -> NonNull<T> {
    let raw_ptr = alloc.allocate_zeroed(Layout::from_size_align(T::static_size_of_val(), T::static_align_of_val()).unwrap()).unwrap().as_ptr() as *mut u8;
    NonNull::new(ptr::from_raw_parts_mut(raw_ptr, T::create_implicit_metadata())).unwrap()
}
