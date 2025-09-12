use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock};
use anyhow::anyhow;
use paste::paste;
use gospel_typelib::type_model::{CVQualifiedType, MutableTypeGraph, PrimitiveType, ResolvedUDTMemberLayout, TargetTriplet, Type, TypeLayoutCache, UserDefinedTypeMember};
use crate::memory_access::{Memory, OpaquePtr};

/// Used as a key to hash lookups for the calculation of various forms of layout
#[derive(Debug)]
struct FastLayoutCacheKey<T: Hash + PartialEq + Eq> {
    type_index: usize,
    name: &'static str,
    additional_data: T,
}
impl<T: Hash + PartialEq + Eq> Hash for FastLayoutCacheKey<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.type_index.hash(state);
        self.name.as_ptr().addr().hash(state);
        self.additional_data.hash(state);
    }
}
impl<T: Hash + PartialEq + Eq> PartialEq for FastLayoutCacheKey<T> {
    fn eq(&self, other: &Self) -> bool {
        self.type_index == other.type_index &&
            self.name.as_ptr().addr() == other.name.as_ptr().addr() &&
            self.additional_data == other.additional_data
    }
}
impl<T: Hash + PartialEq + Eq> Eq for FastLayoutCacheKey<T> {}


/// Type ptr namespace represents a type hierarchy used by a hierarchy of related type pointers
#[derive(Clone)]
pub struct TypePtrNamespace {
    pub type_graph: Arc<RwLock<dyn MutableTypeGraph>>,
    pub layout_cache: Arc<RwLock<TypeLayoutCache>>,
    field_layout_cache: Arc<RwLock<HashMap<FastLayoutCacheKey<()>, Option<(usize, usize)>>>>,
    enum_constant_cache: Arc<RwLock<HashMap<FastLayoutCacheKey<()>, Option<u64>>>>,
    static_type_cache: Arc<RwLock<HashMap<usize, Option<usize>>>>,
}
impl TypePtrNamespace {
    /// Creates a new type pointer namespace from the given type graph
    pub fn create(type_graph: Arc<RwLock<dyn MutableTypeGraph>>, target_triplet: TargetTriplet) -> TypePtrNamespace {
        TypePtrNamespace{ type_graph, layout_cache: Arc::new(RwLock::new(TypeLayoutCache::create(target_triplet))), field_layout_cache: Arc::default(), enum_constant_cache: Arc::default(), static_type_cache: Arc::default() }
    }
    /// This function answers the question "by how much do I need to offset pointer to type from_index to get a pointer to type to_index?"
    /// Returns None if two types are not related and their values are not convertible, or pointer adjustment necessary for conversion (in case of upcasting and downcasting)
    /// Note that for indirect pointers to be considered convertible the wrapped pointer types must be convertible with no offset
    /// This has the same rules as static_cast in C++, it will not attempt to reinterpret bits of unrelated types. However, note that unlike static_cast in C++,
    /// this cast will only succeed if no coercion is necessary (e.g. while static_cast from float to int will succeed in C++, it will fail here).
    /// Additionally, it will not convert between pointers and integers
    pub fn get_static_cast_pointer_adjust(&self, from_type_index: usize, to_type_index: usize) -> Option<i64> {
        let type_graph = self.type_graph.read().unwrap();
        let target_triplet = self.layout_cache.read().unwrap().target_triplet.clone();

        let from_base_type_index = type_graph.base_type_index(from_type_index);
        let to_base_type_index = type_graph.base_type_index(to_type_index);

        let from_base_type = type_graph.type_by_index(from_base_type_index);
        let to_base_type = type_graph.type_by_index(to_base_type_index);

        if from_base_type_index == to_base_type_index {
            // Shortcut for when from and to is the same base type
            Some(0)
        } else if let Type::Primitive(from_primitive_type) = from_base_type && let Type::Primitive(to_primitive_type) = to_base_type {
            // Primitive types can only be converted in-place, so their offset is always 0
            if Self::are_primitive_types_convertible(*from_primitive_type, *to_primitive_type, &target_triplet) { Some(0) } else { None }
        } else if let Type::Enum(from_enum_type) = from_base_type && let Type::Primitive(to_primitive_type) = to_base_type {
            // Enum type can be converted to primitive type if its underlying type can be converted to it
            let from_underlying_type = from_enum_type.underlying_type(&target_triplet).unwrap();
            if Self::are_primitive_types_convertible(from_underlying_type, *to_primitive_type, &target_triplet) { Some(0) } else { None }
        } else if let Type::Primitive(from_primitive_type) = from_base_type && let Type::Enum(to_enum_type) = to_base_type {
            // Primitive type can be converted to enum type if it can be converted to its underlying type
            let to_underlying_type = to_enum_type.underlying_type(&target_triplet).unwrap();
            if Self::are_primitive_types_convertible(*from_primitive_type, to_underlying_type, &target_triplet) { Some(0) } else { None }
        } else if let Type::Pointer(from_pointer_type) = from_base_type && let Type::Pointer(to_pointer_type) = to_base_type {
            // Pointer types are only convertible if pointee type can be converted without applying any adjustment
            // Re-entry to get_static_cast_pointer_adjust is okay in this context because read lock that we are holding can be shared
            if self.get_static_cast_pointer_adjust(from_pointer_type.pointee_type_index, to_pointer_type.pointee_type_index) == Some(0) { Some(0) } else { None }
        } else if let Type::Array(from_array_type) = from_base_type && let Type::Array(to_array_type) = to_base_type {
            // Similar logic applies to arrays as it does to pointers, two array types are convertible if their element types are convertible without any adjustment
            // Arrays also have an additional requirement of their length being equal
            if from_array_type.array_length == to_array_type.array_length &&
                self.get_static_cast_pointer_adjust(from_array_type.element_type_index, to_array_type.element_type_index) == Some(0) { Some(0) } else { None }
        } else if let Type::UDT(from_user_defined_type) = from_base_type && let Type::UDT(to_user_defined_type) = to_base_type {
            // Struct types can be upcasted or downcasted. Try upcasting (casting from derived class to base class first) first, and then downcasting (casting from base class to derived class) as a fallback
            let mut layout_cache = self.layout_cache.write().unwrap();
            let base_class_offsets= from_user_defined_type.find_all_base_class_offsets(from_base_type_index, to_base_type_index, type_graph.deref(), layout_cache.deref_mut()).unwrap();
            if  !base_class_offsets.is_empty() {
                // When upcasting, base class is located at positive offset from this pointer. In this case, it is also safe to pick any instance of base class within the derived class, preferring for the outermost first instance
                Some(base_class_offsets[0] as i64)
            } else if let derived_class_offsets = to_user_defined_type.find_all_base_class_offsets(to_base_type_index, from_base_type_index, type_graph.deref(), layout_cache.deref_mut()).unwrap() && derived_class_offsets.len() == 1 {
                // Downcasting can only be performed where there is only once instance of base class in the hierarchy chain. When there are multiple instances, it is not possible to know pointer to which instance we have
                // Downcasting also goes from base to derived class, which is at lower addresses, so the offset here is negative
                Some(-(derived_class_offsets[0] as i64))
            } else {
                // Given UDTs are not related otherwise, and the cast is not possible
                None
            }
        } else {
            // Types are not related otherwise and there is no implicit conversion available
            None
        }
    }
    fn are_primitive_types_convertible(from_primitive_type: PrimitiveType, to_primitive_type: PrimitiveType, target_triplet: &TargetTriplet) -> bool {
        // Primitive types are convertible if they are of the same bit width and integral status. Signedness changing conversions are allowed
        if let Some(from_bit_width) = from_primitive_type.bit_width(&target_triplet) &&
            let Some(to_bit_width) = to_primitive_type.bit_width(&target_triplet) &&
            from_bit_width == to_bit_width && from_primitive_type.is_integral() == to_primitive_type.is_integral() {
            return true;
        }
        // Otherwise, primitive types are convertible if they are the exact same type, or to type is void
        if from_primitive_type == to_primitive_type || to_primitive_type == PrimitiveType::Void {
            return true;
        }
        false
    }
    /// Reads the value of the enum constant with the given name at specified enum type index, and returns it
    pub fn get_enum_type_constant_value(&self, enum_type_index: usize, constant_name: &str) -> Option<u64> {
        let type_graph = self.type_graph.read().unwrap();
        let layout_cache = self.layout_cache.read().unwrap();
        if let Type::Enum(enum_type) = type_graph.base_type_by_index(enum_type_index) {
            if let Some(constant) = enum_type.constants.iter().find(|x| x.name.as_ref().map(|y| y.as_ref()) == Some(constant_name)) {
                Some(enum_type.constant_value(constant, &layout_cache.target_triplet).unwrap())
            } else { None }
        } else { None }
    }
    pub fn get_enum_type_constant_value_cached(&self, enum_type_index: usize, constant_name: &'static str) -> Option<u64> {
        let cache_key = FastLayoutCacheKey{type_index: enum_type_index, name: constant_name, additional_data: ()};
        if let Some(existing_constant_value) = self.enum_constant_cache.read().unwrap().get(&cache_key) {
            existing_constant_value.clone()
        } else {
            let enum_constant_value = self.get_enum_type_constant_value(enum_type_index, constant_name);
            self.enum_constant_cache.write().unwrap().insert(cache_key, enum_constant_value.clone());
            enum_constant_value
        }
    }
    pub fn get_static_type_index_cached(&self, full_type_name: &'static str) -> Option<usize> {
        let cache_key = full_type_name.as_ptr().addr();
        if let Some(existing_static_type_index) = self.static_type_cache.read().unwrap().get(&cache_key) {
            existing_static_type_index.clone()
        } else {
            let mut type_graph = self.type_graph.write().unwrap();
            let new_type_index = type_graph.create_named_type(full_type_name, vec![]).unwrap();
            self.static_type_cache.write().unwrap().insert(cache_key, new_type_index.clone());
            new_type_index
        }
    }
}

#[derive(Clone)]
pub struct TypePtrMetadata {
    pub namespace: TypePtrNamespace,
    pub type_index: usize,
}
impl TypePtrMetadata {
    pub fn with_type_index(&self, type_index: usize) -> Self {
        Self{namespace: self.namespace.clone(), type_index}
    }
    pub fn with_type_index_and_cv_qualifiers(&self, new_type_index: usize) -> TypePtrMetadata {
        let mut type_graph = self.namespace.type_graph.write().unwrap();
        let base_new_type_index = type_graph.base_type_index(new_type_index);
        if let Some(cv_qualified_type) = type_graph.cv_qualified_type_at_index(self.type_index) {
            let cv_qualified_new_type_index = type_graph.store_type(Type::CVQualified(CVQualifiedType{
                base_type_index: base_new_type_index,
                constant: cv_qualified_type.constant,
                volatile: cv_qualified_type.volatile,
            }));
            self.with_type_index(cv_qualified_new_type_index)
        } else {
            self.with_type_index(base_new_type_index)
        }
    }
    pub fn base_type_index(&self) -> usize {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let type_data = type_graph.type_by_index(self.type_index);
        if let Type::CVQualified(cv_qualified_type) = type_data {
            cv_qualified_type.base_type_index
        } else { self.type_index }
    }
    pub fn size_and_alignment(&self) -> (usize, usize) {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let mut layout_cache = self.namespace.layout_cache.write().unwrap();
        let base_type_index = type_graph.base_type_index(self.type_index);
        Type::size_and_alignment(base_type_index, type_graph.deref(), layout_cache.deref_mut()).unwrap()
    }
    pub fn primitive_type_and_size(&self) -> Option<(PrimitiveType, usize)> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let layout_cache = self.namespace.layout_cache.read().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Primitive(primitive_type) = type_data {
            Some((primitive_type.clone(), primitive_type.size_and_alignment(&layout_cache.target_triplet).unwrap()))
        } else if let Type::Enum(enum_type) = type_data {
            let underlying_primitive_type = enum_type.underlying_type(&layout_cache.target_triplet).unwrap();
            Some((underlying_primitive_type, underlying_primitive_type.size_and_alignment(&layout_cache.target_triplet).unwrap()))
        } else { None }
    }
    pub fn pointer_pointee_type_index_and_is_reference(&self) -> Option<(usize, bool)> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Pointer(pointer_type) = type_data {
            Some((pointer_type.pointee_type_index, pointer_type.is_reference))
        } else { None }
    }
    pub fn array_element_type_index(&self) -> Option<usize> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Some(array_type.element_type_index)
        } else { None }
    }
    pub fn array_static_array_length(&self) -> Option<usize> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Some(array_type.array_length)
        } else { None }
    }
    pub fn struct_type_name(&self) -> Option<String> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.name.clone()
        } else { None }
    }
    pub fn struct_find_all_base_classes_by_type_name(&self, full_base_class_type_name: &str) -> Option<Vec<usize>> {
        let type_graph = self.namespace.type_graph.read().unwrap();
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
    pub fn struct_field_type_index_and_offset(&self, field_name: &str) -> Option<(usize, usize)> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let mut layout_cache = self.namespace.layout_cache.write().unwrap();
        let base_type_index = type_graph.base_type_index(self.type_index);
        let type_data = type_graph.type_by_index(base_type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_map_member_layout(base_type_index, field_name, &|context| {
                if let UserDefinedTypeMember::Field(field) = &context.owner_udt.members[context.member_index] &&
                    let ResolvedUDTMemberLayout::Field(field_layout) = &context.owner_layout.member_layouts[context.member_index] {
                    Some((field.member_type_index, context.owner_offset + field_layout.offset))
                } else { None }
            }, type_graph.deref(), layout_cache.deref_mut()).unwrap()
        } else { None }
    }
    pub fn struct_field_type_index_and_offset_cached(&self, field_name: &'static str) -> Option<(usize, usize)> {
        let layout_cache = FastLayoutCacheKey{type_index: self.type_index, name: field_name, additional_data: ()};
        if let Some(existing_layout) = self.namespace.field_layout_cache.read().unwrap().get(&layout_cache) {
            existing_layout.clone()
        } else {
            let field_layout = self.struct_field_type_index_and_offset(field_name);
            self.namespace.field_layout_cache.write().unwrap().insert(layout_cache, field_layout.clone());
            field_layout
        }
    }
}

macro_rules! implement_dynamic_ptr_numeric_access {
    ($data_type: ident, $is_integral: literal, $is_floating_point: literal) => {
        paste! {
            pub fn [<read_ $data_type>](&self) -> anyhow::Result<Option<$data_type>> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    Ok(Some(self.opaque_ptr.[<read_ $data_type>]()?))
                } else { Ok(None) }
            }
            pub fn [<read_ $data_type _slice_unchecked>](&self, buffer: &mut [$data_type]) -> anyhow::Result<bool> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    self.opaque_ptr.[<read_ $data_type _array>](buffer)?;
                    Ok(true)
                } else { Ok(false) }
            }
            pub fn [<write_ $data_type>](&self, value: $data_type) -> anyhow::Result<()> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    self.opaque_ptr.[<write_ $data_type>](value)
                } else { Err(anyhow!("Not an integral type of the matching bit width")) }
            }
            pub fn [<write_ $data_type _slice_unchecked>](&self, buffer: &[$data_type]) -> anyhow::Result<()> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    self.opaque_ptr.[<write_ $data_type _array>](buffer)
                } else { Err(anyhow!("Not an integral type of the matching bit width")) }
            }
        }
    };
}

pub struct DynamicPtr<M: Memory> {
    pub opaque_ptr: OpaquePtr<M>,
    pub metadata: TypePtrMetadata,
}
impl<M: Memory> Clone for DynamicPtr<M> {
    fn clone(&self) -> Self {
        Self {
            opaque_ptr: self.opaque_ptr.clone(),
            metadata: self.metadata.clone(),
        }
    }
}
impl<M: Memory> PartialEq for DynamicPtr<M> {
    fn eq(&self, other: &Self) -> bool {
        self.opaque_ptr == other.opaque_ptr
    }
}
impl<M: Memory> Eq for DynamicPtr<M> {}
impl<M: Memory> PartialOrd for DynamicPtr<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.opaque_ptr.partial_cmp(&other.opaque_ptr)
    }
}
impl<M: Memory> Ord for DynamicPtr<M> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.opaque_ptr.cmp(&other.opaque_ptr)
    }
}
impl<M: Memory> Hash for DynamicPtr<M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.opaque_ptr.hash(state)
    }
}
impl<M: Memory> DynamicPtr<M> {
    /// Returns true if this pointer points to zero address, e.g. is a nullptr
    pub fn is_nullptr(&self) -> bool {
        self.opaque_ptr.is_nullptr()
    }
    /// Creates a nullptr from this pointer, copying its type information and memory backend, but setting the address to 0
    pub fn to_nullptr(&self) -> Self {
        DynamicPtr{opaque_ptr: OpaquePtr{memory: self.opaque_ptr.memory.clone(), address: 0}, metadata: self.metadata.clone()}
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> Self {
        Self{opaque_ptr: self.opaque_ptr.clone() + (count * self.metadata.size_and_alignment().0), metadata: self.metadata.clone() }
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> Self {
        Self{opaque_ptr: self.opaque_ptr.clone() - (count * self.metadata.size_and_alignment().0), metadata: self.metadata.clone() }
    }
    /// Returns the pointer to the array element at the given index. Performs boundaries check
    pub fn get_array_element_ptr(&self, array_element_index: usize) -> Option<Self> {
        if let Some(static_array_length) = self.metadata.array_static_array_length() && array_element_index < static_array_length {
            Some(self.add_unchecked(array_element_index))
        } else { None }
    }
    /// Returns the pointer to the struct field with the given name
    pub fn get_struct_field_ptr(&self, field_name: &str) -> Option<Self> {
        if let Some((field_type_index, field_offset)) = self.metadata.struct_field_type_index_and_offset(field_name) {
            Some(Self{opaque_ptr: self.opaque_ptr.clone() + field_offset, metadata: self.metadata.with_type_index(field_type_index)})
        } else { None }
    }
    /// Returns the pointer to the struct field with the given name. Caches the result by string ptr
    pub fn get_struct_field_ptr_cached(&self, field_name: &'static str) -> Option<Self> {
        if let Some((field_type_index, field_offset)) = self.metadata.struct_field_type_index_and_offset_cached(field_name) {
            Some(Self{opaque_ptr: self.opaque_ptr.clone() + field_offset, metadata: self.metadata.with_type_index(field_type_index)})
        } else { None }
    }
    /// Attempts to read this dynamic pointer as a pointer
    pub fn read_ptr(&self) -> anyhow::Result<Option<Self>> {
        if let Some((pointee_type_index, _)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            let pointee_opaque_ptr = self.opaque_ptr.read_ptr()?;
            Ok(Some(Self{opaque_ptr: pointee_opaque_ptr, metadata: self.metadata.with_type_index(pointee_type_index)}))
        } else { Ok(None) }
    }
    pub fn read_ptr_slice_unchecked(&self, len: usize) -> anyhow::Result<Option<Vec<Option<Self>>>> {
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            let element_metadata = self.metadata.with_type_index(pointee_type_index);
            Ok(Some(self.opaque_ptr.read_ptr_array(len)?.into_iter().map(|x| {
                if x.is_nullptr() {
                    if is_reference_type {
                        Err(anyhow!("Reference type has illegal value of nullptr"))
                    } else { Ok(None) }
                } else {
                    Ok(Some(Self{opaque_ptr: x, metadata: element_metadata.clone()}))
                }
            }).collect::<anyhow::Result<Vec<Option<Self>>>>()?))
        } else { Ok(None) }
    }
    /// Attempts to write this dynamic pointer as a pointer value. Writes address of given ptr as a value
    pub fn write_ptr(&self, value: &Self) -> anyhow::Result<()> {
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            if value.is_nullptr() && is_reference_type {
                Err(anyhow!("Cannot write value of nullptr to reference type"))
            } else if let Some(other_pointer_adjust) = self.metadata.namespace.get_static_cast_pointer_adjust(value.metadata.type_index, pointee_type_index) {
                self.opaque_ptr.write_ptr(&(value.opaque_ptr.clone() + other_pointer_adjust))
            } else { Err(anyhow!("Pointee type is not compatible")) }
        } else { Err(anyhow!("Not a pointer type")) }
    }
    /// Attempts to write this dynamic pointer as a pointer value. Writes 0 address (nullptr) as a value
    pub fn write_nullptr(&self) -> anyhow::Result<()> {
        if let Some((_, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            if is_reference_type {
                Err(anyhow!("Cannot write value of nullptr to reference type"))
            } else { self.opaque_ptr.write_nullptr() }
        } else { Err(anyhow!("Not a pointer type")) }
    }
    pub fn write_ptr_slice_unchecked(&self, buffer: &[Self]) -> anyhow::Result<()> {
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            let raw_ptr_array: Vec<OpaquePtr<M>> = buffer.iter().map(|element_ptr| {
                if element_ptr.is_nullptr() && is_reference_type {
                    Err(anyhow!("Cannot write value of nullptr to reference type"))
                } else if let Some(other_pointer_adjust) = self.metadata.namespace.get_static_cast_pointer_adjust(element_ptr.metadata.type_index, pointee_type_index) {
                    Ok(element_ptr.opaque_ptr.clone() + other_pointer_adjust)
                } else { Err(anyhow!("Pointee type is not compatible")) }
            }).collect::<anyhow::Result<Vec<OpaquePtr<M>>>>()?;
            self.opaque_ptr.write_ptr_array(raw_ptr_array.as_slice())
        } else { Err(anyhow!("Not a pointer type")) }
    }

    pub fn read_integral_type(&self) -> anyhow::Result<Option<u64>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => Ok(Some(self.opaque_ptr.read_u8()? as u64)),
                2 => Ok(Some(self.opaque_ptr.read_u16()? as u64)),
                4 => Ok(Some(self.opaque_ptr.read_u32()? as u64)),
                8 => Ok(Some(self.opaque_ptr.read_u64()?)),
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Ok(None) }
    }
    pub fn read_integral_type_slice_unchecked(&self, buffer: &mut [u64]) -> anyhow::Result<bool> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => {
                    let mut underlying_buffer: Box<[u8]> = vec![0u8; buffer.len()].into_boxed_slice();
                    self.opaque_ptr.read_u8_array(underlying_buffer.deref_mut())?;
                    for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                    Ok(true)
                },
                2 => {
                    let mut underlying_buffer: Box<[u16]> = vec![0u16; buffer.len()].into_boxed_slice();
                    self.opaque_ptr.read_u16_array(underlying_buffer.deref_mut())?;
                    for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                    Ok(true)
                },
                4 => {
                    let mut underlying_buffer: Box<[u32]> = vec![0u32; buffer.len()].into_boxed_slice();
                    self.opaque_ptr.read_u32_array(underlying_buffer.deref_mut())?;
                    for element_index in 0..buffer.len() { buffer[element_index] = underlying_buffer[element_index] as u64; }
                    Ok(true)
                },
                8 => {
                    self.opaque_ptr.read_u64_array(buffer)?;
                    Ok(true)
                },
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Ok(false) }
    }
    pub fn write_integral_type(&self, value: u64) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => self.opaque_ptr.write_u8(value as u8),
                2 => self.opaque_ptr.write_u16(value as u16),
                4 => self.opaque_ptr.write_u32(value as u32),
                8 => self.opaque_ptr.write_u64(value),
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Err(anyhow!("Not an integral type")) }
    }
    pub fn write_integral_type_slice_unchecked(&self, buffer: &[u64]) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size() && primitive_type.is_integral() {
            match primitive_size {
                1 => {
                    let mut underlying_buffer: Box<[u8]> = vec![0u8; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u8; }
                    self.opaque_ptr.write_u8_array(underlying_buffer.deref())?;
                    Ok({})
                },
                2 => {
                    let mut underlying_buffer: Box<[u16]> = vec![0u16; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u16; }
                    self.opaque_ptr.write_u16_array(underlying_buffer.deref())?;
                    Ok({})
                },
                4 => {
                    let mut underlying_buffer: Box<[u32]> = vec![0u32; buffer.len()].into_boxed_slice();
                    for element_index in 0..buffer.len() { underlying_buffer[element_index] = buffer[element_index] as u32; }
                    self.opaque_ptr.write_u32_array(underlying_buffer.deref())?;
                    Ok({})
                },
                8 => {
                    self.opaque_ptr.write_u64_array(buffer)?;
                    Ok({})
                },
                _ => Err(anyhow!("unknown integral primitive size"))
            }
        } else { Err(anyhow!("Not an integral type")) }
    }

    implement_dynamic_ptr_numeric_access!(u8, true, false);
    implement_dynamic_ptr_numeric_access!(u16, true, false);
    implement_dynamic_ptr_numeric_access!(u32, true, false);
    implement_dynamic_ptr_numeric_access!(u64, true, false);
    implement_dynamic_ptr_numeric_access!(i8, true, false);
    implement_dynamic_ptr_numeric_access!(i16, true, false);
    implement_dynamic_ptr_numeric_access!(i32, true, false);
    implement_dynamic_ptr_numeric_access!(i64, true, false);
    implement_dynamic_ptr_numeric_access!(f32, false, true);
    implement_dynamic_ptr_numeric_access!(f64, false, true);
}
