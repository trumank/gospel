use std::alloc::{Allocator, Layout};
use std::marker::{PhantomData};
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::{mem, ptr};
use std::clone::CloneToUninit;
use std::ptr::{NonNull, Pointee};
use std::sync::{Mutex, RwLock};
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicU64, AtomicUsize, Ordering};
use generic_statics::Zeroable;
use gospel_typelib::compiled_target_triplet;
use gospel_typelib::target_triplet::TargetTriplet;
use gospel_typelib::type_model::{ArrayType, IntegerSignedness, MutableTypeGraph, PointerType, PrimitiveType, Type};
use crate::core_type_definitions::{implement_enum_underlying_type, implement_primitive_type_tag, EnumUnderlyingType, IntegralValueTypeTag, StaticTypeLayoutCache, StaticTypeTag};

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

implement_enum_underlying_type!(PlatformLongInt, PlatformLongIntUnderlyingType);
implement_enum_underlying_type!(PlatformUnsignedLongInt, PlatformUnsignedLongIntUnderlyingType);
implement_enum_underlying_type!(PlatformWideChar, PlatformWideCharUnderlyingType);

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
/// Static type tag implementation for C reference type
impl<T : ?Sized + ImplicitPtrMetadata + StaticTypeTag> StaticTypeTag for CRef<T> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: true}))
    }
}
/// Reference type wrapped in Option is a pointer
impl<T : ?Sized + ImplicitPtrMetadata + StaticTypeTag> StaticTypeTag for Option<CRef<T>> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let pointee_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Pointer(PointerType{pointee_type_index, is_reference: false}))
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

/// Trait that allows dynamically sized types to be default-constructed at the arbitrary memory location represented as a pointer
pub unsafe trait DefaultConstructAtUninit {
    /// Called to construct the value of this type at the given memory location
    unsafe fn default_construct_at(dest: *mut u8);
}
/// Default specialization of DefaultConstructAtUninit for sized types with Default value
unsafe impl<T : Default> DefaultConstructAtUninit for T {
    unsafe fn default_construct_at(dest: *mut u8) {
        let result_ptr = dest as *mut T;
        unsafe { result_ptr.write(T::default()); }
    }
}

/// Allocates a slice of memory using the size and alignment requirements of the given type
pub fn allocate_uninitialized<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: &A) -> *mut u8 {
    alloc.allocate(Layout::from_size_align(T::static_size_of_val(), T::static_align_of_val()).unwrap()).unwrap().as_ptr() as *mut u8
}

/// Allocates a slice of memory using the size and alignment requirements of the given type. Function is not safe because it does not ensure that zeroed out memory is a valid value of type T
pub unsafe fn allocate_zeroed<T : ?Sized + ImplicitPtrMetadata, A : Allocator>(alloc: &A) -> NonNull<T> {
    let result_ptr = allocate_uninitialized::<T, A>(alloc);
    unsafe { result_ptr.write_bytes(0, T::static_size_of_val()) };
    NonNull::new(ptr::from_raw_parts_mut(result_ptr, T::create_implicit_metadata())).unwrap()
}

/// Allocates a default instance of the given type and returns a raw pointer to it. Value must be manually dropped and memory freed
pub fn allocate_default_raw<T : ?Sized + ImplicitPtrMetadata + DefaultConstructAtUninit, A : Allocator>(alloc: &A) -> NonNull<T> {
    let value_storage_memory = allocate_uninitialized::<T, A>(alloc);
    unsafe { T::default_construct_at(value_storage_memory); }
    NonNull::new(ptr::from_raw_parts_mut(value_storage_memory, T::create_implicit_metadata())).unwrap()
}

/// Allocates a default instance of the given type and returns a box owning the value
pub fn allocate_default<T : ?Sized + ImplicitPtrMetadata + DefaultConstructAtUninit, A : Allocator>(alloc: A) -> Box<T, A> {
    let owned_ptr = allocate_default_raw::<T, A>(&alloc);
    unsafe { Box::<T, A>::from_non_null_in(owned_ptr, alloc) }
}

/// Clones the reference to the unsized value to the memory location allocated from the given allocator. Returns a raw pointer to the resulting value. Value must be manually dropped and memory freed
pub fn clone_unsized_raw<T : ?Sized + ImplicitPtrMetadata + CloneToUninit, A : Allocator>(src: &T, alloc: &A) -> NonNull<T> {
    let dest_memory = allocate_uninitialized::<T, A>(alloc);
    unsafe { src.clone_to_uninit(dest_memory); }
    NonNull::new(ptr::from_raw_parts_mut(dest_memory, T::create_implicit_metadata())).unwrap()
}

/// Clones the reference to the unsized value to the memory location allocated from the given allocator and returns a box owning the value
pub fn clone_unsized<T : ?Sized + ImplicitPtrMetadata + CloneToUninit, A : Allocator>(src: &T, alloc: A) -> Box<T, A> {
    let owned_ptr = clone_unsized_raw::<T, A>(src, &alloc);
    unsafe { Box::<T, A>::from_non_null_in(owned_ptr, alloc) }
}

/// Represents a statically sized C or C++ array, which is a linear sequence of values of type T
pub struct StaticArray<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> {
    phantom_data_array_count: PhantomData<N>,
    phantom_data_element_type: PhantomData<T>,
    private_bytes: [u8],
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> StaticArray<T, N> {
    /// Returns the length of this statically sized array
    pub fn static_len() -> usize {
        N::get_raw_integral_value() as usize
    }
    /// Returns the length of this array
    pub fn len(&self) -> usize {
        Self::static_len()
    }
    /// Returns a const pointer to the array element at index. Will panic if index is out of bounds
    pub fn element_ptr(&self, index: usize) -> *const T {
        assert!(index < Self::static_len());
        let data_ptr = unsafe { self.private_bytes.as_ptr().byte_offset((T::static_size_of_val() * index) as isize) };
        ptr::from_raw_parts::<T>(data_ptr, T::create_implicit_metadata())
    }
    /// Returns a mut pointer to the array element at index. Will panic if index is out of bounds
    pub fn element_mut_ptr(&mut self, index: usize) -> *mut T {
        assert!(index < Self::static_len());
        let data_ptr = unsafe { self.private_bytes.as_mut_ptr().offset((T::static_size_of_val() * index) as isize) };
        ptr::from_raw_parts_mut::<T>(data_ptr, T::create_implicit_metadata())
    }
}
impl<T : ImplicitPtrMetadata, N : IntegralValueTypeTag> ImplicitPtrMetadata for StaticArray<T, N> {
    fn create_implicit_metadata() -> Self::Metadata {
        T::static_size_of_val() * Self::static_len() // array DST size is size of the element multiplied by the number of elements
    }
    fn static_align_of_val() -> usize {
        T::static_align_of_val() // copy the alignment from our element type
    }
}
impl<T : ImplicitPtrMetadata, N : IntegralValueTypeTag> Drop for StaticArray<T, N> {
    fn drop(&mut self) {
        // Execute destructor for each array element
        for index in 0..Self::static_len() {
            unsafe { self.element_mut_ptr(index).drop_in_place() }
        }
    }
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> Index<usize> for StaticArray<T, N> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.element_ptr(index).as_ref().unwrap() }
    }
}
impl<T : ImplicitPtrMetadata, N: IntegralValueTypeTag> IndexMut<usize> for StaticArray<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.element_mut_ptr(index).as_mut().unwrap() }
    }
}
impl<T : StaticTypeTag + ImplicitPtrMetadata, N: IntegralValueTypeTag> StaticTypeTag for StaticArray<T, N> {
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
        let element_type_index = T::store_type_descriptor_raw(type_graph, target_triplet, type_cache);
        let array_length = N::get_raw_integral_value() as usize;
        let mut writeable_type_graph = type_graph.write().unwrap();
        writeable_type_graph.store_type(Type::Array(ArrayType{element_type_index, array_length}))
    }
}
unsafe impl<T : StaticTypeTag + ImplicitPtrMetadata + DefaultConstructAtUninit, N : IntegralValueTypeTag> DefaultConstructAtUninit for StaticArray<T, N> {
    unsafe fn default_construct_at(dest: *mut u8) {
        // Call default constructor on each individual array element
        for index in 0..Self::static_len() {
            let element_ptr = unsafe { dest.byte_offset((T::static_size_of_val() * index) as isize) };
            unsafe { T::default_construct_at(element_ptr); }
        }
    }
}

/// Represents a reference to a value of opaque type with the given lifetime and the specified type index in the given type universe
pub struct DynRef<'a, TU : TypeUniverse> {
    opaque_value: &'a [u8],
    type_index: usize,
    type_universe_phantom_data: PhantomData<TU>,
}
impl<'a, TU : TypeUniverse> DynRef<'a, TU> {
    /// Attempts to cast the value referenced by this dynamic reference to the given type
    pub fn static_cast<T : StaticTypeTag + ImplicitPtrMetadata>(&self) -> Option<&'a T> {
        let to_type_index = T::store_type_descriptor_to_universe::<TU>();
        let this_pointer_adjust = TU::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(TU::type_graph(), self.type_index, to_type_index)?;
        let adjusted_raw_this_ptr = unsafe { self.opaque_value.as_ptr().byte_offset(this_pointer_adjust as isize) };
        let adjusted_this_ptr = ptr::from_raw_parts::<T>(adjusted_raw_this_ptr, T::create_implicit_metadata());
        Some(unsafe { adjusted_this_ptr.as_ref_unchecked::<'a>() })
    }
}

/// Represents a mutable reference to a value of opaque type with the given lifetime and the specified type index in the given type universe
pub struct DynMut<'a, TU : TypeUniverse> {
    opaque_value: &'a mut [u8],
    type_index: usize,
    type_universe_phantom_data: PhantomData<TU>,
}
impl<'a, TU : TypeUniverse> DynMut<'a, TU> {
    /// Attempts to cast the value referenced by this dynamic reference to the given type
    pub fn static_cast<T : StaticTypeTag + ImplicitPtrMetadata>(&mut self) -> Option<&'a mut T> {
        let to_type_index = T::store_type_descriptor_to_universe::<TU>();
        let this_pointer_adjust = TU::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(TU::type_graph(), self.type_index, to_type_index)?;


        let adjusted_raw_this_ptr = unsafe { self.opaque_value.as_mut_ptr().byte_offset(this_pointer_adjust as isize) };
        let adjusted_this_ptr = ptr::from_raw_parts_mut::<T>(adjusted_raw_this_ptr, T::create_implicit_metadata());
        Some(unsafe { adjusted_this_ptr.as_mut_unchecked::<'a>() })
    }
}

/// Calculates size of the given type with the static type tag in the given type universe
pub fn calc_type_size_and_alignment<T : StaticTypeTag, U : TypeUniverse>() -> (usize, usize) {
    let type_index = T::store_type_descriptor_to_universe::<U>();
    U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), type_index)
}

/// Calculates the value of the enum constant with the given name
pub fn calc_enum_constant_value<T : StaticTypeTag, U : TypeUniverse>(constant_name: &'static str) -> Option<u64> {
    let type_index = T::store_type_descriptor_to_universe::<U>();
    U::type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(U::type_graph(), type_index, constant_name)
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeTypeSizeAndAlignment<T: StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    type_size: AtomicUsize,
    type_alignment: AtomicUsize,
    is_enum_type: AtomicBool,
    is_enum_underlying_type_signed: AtomicBool,
    _phantom_data_type: PhantomData<T>,
    _phantom_data_type_universe: PhantomData<U>,
}
unsafe impl<T: StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeTypeSizeAndAlignment<T, U> {}
impl<T: StaticTypeTag, U : TypeUniverse> CachedThreadSafeTypeSizeAndAlignment<T, U> {
    pub fn get_type_size_and_alignment(&self) -> (usize, usize) {
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();
            let (type_size, type_alignment) = U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), type_index);
            let (is_enum_type, is_underlying_type_signed) = if let Type::Enum(enum_type) = U::type_graph().read().unwrap().type_by_index(type_index).clone() {
                (true, enum_type.underlying_type(&U::target_triplet()).unwrap().integer_signedness().unwrap() == IntegerSignedness::Signed)
            } else { (false, false) };
            self.is_enum_type.store(is_enum_type, Ordering::Relaxed);
            self.is_enum_underlying_type_signed.store(is_underlying_type_signed, Ordering::Relaxed);
            self.type_size.store(type_size, Ordering::Relaxed);
            self.type_alignment.store(type_alignment, Ordering::Relaxed);
            self.has_value_cached.store(true, Ordering::Release);
        }
        (self.type_size.load(Ordering::Relaxed), self.type_alignment.load(Ordering::Relaxed))
    }
}
impl<T : StaticTypeTag + ImplicitPtrMetadata, U : TypeUniverse> CachedThreadSafeTypeSizeAndAlignment<T, U> {
    /// Creates an enum value initialized from the raw discriminant in the given allocator
    pub fn create_boxed_enum_value<A: Allocator>(&self, raw_discriminant: u64, alloc: A) -> Box<T, A> {
        // Although type size could also be derived from ImplicitPtrMetadata, we have to call get_type_size_and_alignment to calculate enum-specific fields
        let (underlying_type_size, _) = self.get_type_size_and_alignment();
        assert!(self.is_enum_type.load(Ordering::Relaxed));
        let is_underlying_type_signed = self.is_enum_underlying_type_signed.load(Ordering::Relaxed);

        let raw_value_ptr = allocate_uninitialized::<T, A>(&alloc);
        match is_underlying_type_signed {
            true => match underlying_type_size {
                1 => unsafe { (raw_value_ptr as *mut i8).write(i8::from_raw_discriminant(raw_discriminant)); }
                2 => unsafe { (raw_value_ptr as *mut i16).write(i16::from_raw_discriminant(raw_discriminant)); }
                4 => unsafe { (raw_value_ptr as *mut i32).write(i32::from_raw_discriminant(raw_discriminant)); }
                8 => unsafe { (raw_value_ptr as *mut i64).write(i64::from_raw_discriminant(raw_discriminant)); }
                _ => { unreachable!(); }
            }
            false => match underlying_type_size {
                1 => unsafe { raw_value_ptr.write(u8::from_raw_discriminant(raw_discriminant)); }
                2 => unsafe { (raw_value_ptr as *mut u16).write(u16::from_raw_discriminant(raw_discriminant)); }
                4 => unsafe { (raw_value_ptr as *mut u32).write(u32::from_raw_discriminant(raw_discriminant)); }
                8 => unsafe { (raw_value_ptr as *mut u64).write(u64::from_raw_discriminant(raw_discriminant)); }
                _ => { unreachable!(); }
            }
        };
        let value_ptr = ptr::from_raw_parts_mut::<T>(raw_value_ptr, T::create_implicit_metadata());
        unsafe { Box::from_raw_in(value_ptr, alloc) }
    }
    /// Reads an enum value into a raw discriminant value
    pub fn read_boxed_enum_value(&self, enum_value: &T) -> u64 {
        // Although type size could also be derived from ImplicitPtrMetadata, we have to call get_type_size_and_alignment to calculate enum-specific fields
        let (underlying_type_size, _) = self.get_type_size_and_alignment();
        assert!(self.is_enum_type.load(Ordering::Relaxed));
        let is_underlying_type_signed = self.is_enum_underlying_type_signed.load(Ordering::Relaxed);
        let raw_enum_value_ptr = enum_value as *const T;

        match is_underlying_type_signed {
            true => match underlying_type_size {
                1 => unsafe { (raw_enum_value_ptr as *const i8).read().to_raw_discriminant() }
                2 => unsafe { (raw_enum_value_ptr as *const i16).read().to_raw_discriminant() }
                4 => unsafe { (raw_enum_value_ptr as *const i32).read().to_raw_discriminant() }
                8 => unsafe { (raw_enum_value_ptr as *const i64).read().to_raw_discriminant() }
                _ => { unreachable!(); }
            }
            false => match underlying_type_size {
                1 => unsafe { (raw_enum_value_ptr as *const u8).read().to_raw_discriminant() }
                2 => unsafe { (raw_enum_value_ptr as *const u16).read().to_raw_discriminant() }
                4 => unsafe { (raw_enum_value_ptr as *const u32).read().to_raw_discriminant() }
                8 => unsafe { (raw_enum_value_ptr as *const u64).read().to_raw_discriminant() }
                _ => { unreachable!(); }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeStaticCastThisAdjust<From : StaticTypeTag, To: StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_cast_possible: AtomicBool,
    cast_this_adjust: AtomicIsize,
    _phantom_data_from: PhantomData<From>,
    _phantom_data_to: PhantomData<To>,
    _phantom_data_type_universe: PhantomData<U>,
}
unsafe impl<From : StaticTypeTag, To: StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeStaticCastThisAdjust<From, To, U> {}
impl<From : StaticTypeTag, To: StaticTypeTag, U : TypeUniverse> CachedThreadSafeStaticCastThisAdjust<From, To, U> {
    pub fn get_static_cast_this_adjust(&self) -> Option<isize> {
        if !self.has_value_cached.load(Ordering::Acquire) {
            let from_type_index = From::store_type_descriptor_to_universe::<U>();
            let to_type_index = To::store_type_descriptor_to_universe::<U>();
            if let Some(static_cast_adjust) = U::type_layout_cache().lock().unwrap().get_static_cast_pointer_adjust(U::type_graph(), from_type_index, to_type_index) {
                self.result_cast_possible.store(true, Ordering::Relaxed);
                self.cast_this_adjust.store(static_cast_adjust as isize, Ordering::Relaxed);
            } else {
                self.result_cast_possible.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        if self.result_cast_possible.load(Ordering::Relaxed) {
            Some(self.cast_this_adjust.load(Ordering::Relaxed))
        } else { None }
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeFieldTypeAndOffset<T : StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_has_field: AtomicBool,
    field_type_index: AtomicUsize,
    field_offset_bytes: AtomicUsize,
    field_size_bytes: AtomicUsize,
    _phantom_udt_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
unsafe impl<T : StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeFieldTypeAndOffset<T, U> {}
impl<T : StaticTypeTag, U : TypeUniverse> CachedThreadSafeFieldTypeAndOffset<T, U> {
    pub fn get_field_type_index_offset_and_size(&self, field_name: &'static str) -> Option<(usize, usize, usize)> {
        // If there is no value cached, we have to calculate the value here and then release the has_value_cached to make the results visible to other threads
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();

            // We want relaxed ordering here since they will be ordered by has_value_cached anyway
            if let Some((field_type_index, field_offset_bytes)) = U::type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(U::type_graph(), type_index, field_name) {
                let field_size_bytes = U::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(U::type_graph(), field_type_index).0;
                self.result_has_field.store(true, Ordering::Relaxed);
                self.field_type_index.store(field_type_index, Ordering::Relaxed);
                self.field_offset_bytes.store(field_offset_bytes, Ordering::Relaxed);
                self.field_size_bytes.store(field_size_bytes, Ordering::Relaxed);
            } else {
                self.result_has_field.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        if self.result_has_field.load(Ordering::Relaxed) {
            Some((self.field_type_index.load(Ordering::Relaxed), self.field_offset_bytes.load(Ordering::Relaxed), self.field_size_bytes.load(Ordering::Relaxed)))
        } else { None }
    }
    /// Returns the reference to the field with the given name from the base reference and the field name
    pub fn get_field_ref<'a, F : ImplicitPtrMetadata>(&self, base_ref: &'a T, field_name: &'static str) -> Option<&'a F> {
        let (_, field_offset_bytes, _) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *const T as *const u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts::<F>(field_raw_ptr, F::create_implicit_metadata());
        Some(unsafe { field_ptr.as_ref_unchecked::<'a>() })
    }
    /// Returns the mutable reference to the field with the given name from the base reference and the field name
    pub fn get_field_mut<'a, F : ImplicitPtrMetadata>(&self, base_ref: &'a mut T, field_name: &'static str) -> Option<&'a mut F> {
        let (_, field_offset_bytes, _) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *mut T as *mut u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts_mut::<F>(field_raw_ptr, F::create_implicit_metadata());
        Some(unsafe { field_ptr.as_mut_unchecked::<'a>() })
    }
    /// Returns the dynamic reference to the field with the given name from the base reference and the field name
    pub fn get_dyn_ref<'a>(&self, base_ref: &'a T, field_name: &'static str) -> Option<DynRef<'a, U>> {
        let (field_type_index, field_offset_bytes, field_size_bytes) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *const T as *const u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts::<[u8]>(field_raw_ptr, field_size_bytes);
        Some(DynRef{opaque_value: unsafe { field_ptr.as_ref_unchecked::<'a>() }, type_index: field_type_index, type_universe_phantom_data: PhantomData::default()})
    }
    /// Returns the mutable dynamic reference to the field with the given name from the base reference and the field name
    pub fn get_dyn_mut<'a>(&self, base_ref: &'a mut T, field_name: &'static str) -> Option<DynMut<'a, U>> {
        let (field_type_index, field_offset_bytes, field_size_bytes) = self.get_field_type_index_offset_and_size(field_name)?;
        let field_raw_ptr = unsafe { (base_ref as *mut T as *mut u8).byte_offset(field_offset_bytes as isize) };
        let field_ptr = ptr::from_raw_parts_mut::<[u8]>(field_raw_ptr, field_size_bytes);
        Some(DynMut{opaque_value: unsafe { field_ptr.as_mut_unchecked::<'a>() }, type_index: field_type_index, type_universe_phantom_data: PhantomData::default()})
    }
}

#[derive(Debug, Default)]
pub struct CachedThreadSafeEnumConstant<T : StaticTypeTag, U : TypeUniverse> {
    has_value_cached: AtomicBool,
    result_has_constant: AtomicBool,
    constant_value: AtomicU64,
    _phantom_enum_type: PhantomData<T>,
    _phantom_type_universe: PhantomData<U>,
}
unsafe impl<T : StaticTypeTag, U : TypeUniverse> Zeroable for CachedThreadSafeEnumConstant<T, U> {}
impl<T : StaticTypeTag, U : TypeUniverse> CachedThreadSafeEnumConstant<T, U> {
    /// Returns the value of the enum constant with the given name
    pub fn get_enum_constant_value(&self, constant_name: &'static str) -> Option<u64> {
        // If there is no value cached, we have to calculate the value here and then release the has_value_cached to make the results visible to other threads
        if !self.has_value_cached.load(Ordering::Acquire) {
            let type_index = T::store_type_descriptor_to_universe::<U>();

            // We want relaxed ordering here since they will be ordered by has_value_cached anyway
            if let Some(constant_value) = U::type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(U::type_graph(), type_index, constant_name) {
                self.result_has_constant.store(true, Ordering::Relaxed);
                self.constant_value.store(constant_value, Ordering::Relaxed);
            } else {
                self.result_has_constant.store(false, Ordering::Relaxed);
            }
            self.has_value_cached.store(true, Ordering::Release);
        }
        // At this point cached data will always be valid (ensured by Acquire memory semantics)
        if self.result_has_constant.load(Ordering::Relaxed) {
            Some(self.constant_value.load(Ordering::Relaxed))
        } else { None }
    }
}