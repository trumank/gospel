use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock};
use anyhow::anyhow;
use paste::paste;
use gospel_typelib::type_model::{CVQualifiedType, MutableTypeGraph, PrimitiveType, ResolvedUDTMemberLayout, Type, TypeLayoutCache, UserDefinedTypeMember};
use crate::memory_access::{Memory, OpaquePtr};

/// Type ptr namespace represents a type hierarchy used by a hierarchy of related type pointers
#[derive(Clone)]
pub struct TypePtrNamespace {
    pub type_graph: Arc<RwLock<dyn MutableTypeGraph>>,
    pub layout_cache: Arc<RwLock<TypeLayoutCache>>,
}
impl TypePtrNamespace {
    pub fn can_assign_ptr_value(&self, to_pointee_type_index: usize, from_pointee_type_index: usize) -> bool {
        let type_graph = self.type_graph.read().unwrap();
        // TODO: This should be relaxed to allow integral conversions between integers of the same width, as well as enums
        type_graph.base_type_index(to_pointee_type_index) == type_graph.base_type_index(from_pointee_type_index)
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
        let type_data = type_graph.base_type_by_index(self.type_index);
        type_data.size_and_alignment(type_graph.deref(), layout_cache.deref_mut()).unwrap()
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
    pub fn struct_all_base_class_offsets(&self, base_class_type_index: usize) -> Option<Vec<usize>> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let mut layout_cache = self.namespace.layout_cache.write().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            Some(user_defined_type.find_all_base_class_offsets(type_graph.base_type_index(base_class_type_index), type_graph.deref(), layout_cache.deref_mut()).unwrap())
        } else { None }
    }
    pub fn struct_field_type_index_and_offset(&self, field_name: &str) -> Option<(usize, usize)> {
        let type_graph = self.namespace.type_graph.read().unwrap();
        let mut layout_cache = self.namespace.layout_cache.write().unwrap();
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_map_member_layout(field_name, &|context| {
                if let UserDefinedTypeMember::Field(field) = &context.owner_udt.members[context.member_index] &&
                    let ResolvedUDTMemberLayout::Field(field_layout) = &context.owner_layout.member_layouts[context.member_index] {
                    Some((field.member_type_index, context.owner_offset + field_layout.offset))
                } else { None }
            }, type_graph.deref(), layout_cache.deref_mut()).unwrap()
        } else { None }
    }
    pub fn struct_get_upcast_this_add_adjust(&self, base_class_type_index: usize) -> Option<usize> {
        // Check if this is the same type we are attempting to cast to, and return 0 offset in that case
        let type_graph = self.namespace.type_graph.read().unwrap();
        let base_base_class_type_index = type_graph.base_type_index(base_class_type_index);
        if type_graph.base_type_index(self.type_index) == base_base_class_type_index {
            return Some(0);
        }
        // We could have multiple instances of the same base class in the type hierarchy at different levels. In that case, we return the first base class that is valid, even if we have multiple,
        // since in such cases usually the user does not care which instance we get (e.g. if this is an interface-like class with no data)
        if let Some(base_class_offsets) = self.struct_all_base_class_offsets(base_base_class_type_index) && !base_class_offsets.is_empty() {
            Some(base_class_offsets[0])
        } else { None }
    }
    pub fn struct_get_unchecked_downcast_this_sub_adjust(&self, derived_class_type_index: usize) -> Option<usize> {
        // Check if this is the same type we are attempting to cast to, and return 0 offset in that case
        let type_graph = self.namespace.type_graph.read().unwrap();
        let base_derived_class_type_index = type_graph.base_type_index(derived_class_type_index);
        if type_graph.base_type_index(self.type_index) == base_derived_class_type_index {
            return Some(0);
        }
        let derived_class_metadata = self.with_type_index(base_derived_class_type_index);
        let base_class_offsets = derived_class_metadata.struct_all_base_class_offsets(self.type_index).unwrap();
        // We cannot upcast from base class to derived class directly if it appears multiple times in the hierarchy, because we do not know which particular base class this pointer refers to
        if base_class_offsets.len() == 1 { Some(base_class_offsets[0]) } else { None }
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
    /// Attempts to read this dynamic pointer as a pointer
    pub fn read_ptr(&self) -> anyhow::Result<Option<Option<Self>>> {
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() {
            let pointee_opaque_ptr = self.opaque_ptr.read_ptr()?;
            if pointee_opaque_ptr.is_nullptr() {
                if is_reference_type {
                    Err(anyhow!("Reference type has illegal value of nullptr"))
                } else { Ok(Some(None)) }
            } else {
                Ok(Some(Some(Self{opaque_ptr: pointee_opaque_ptr, metadata: self.metadata.with_type_index(pointee_type_index)})))
            }
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
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() &&
            self.metadata.namespace.can_assign_ptr_value(pointee_type_index, value.metadata.type_index) {
            if value.is_nullptr() && is_reference_type {
                Err(anyhow!("Cannot write value of nullptr to reference type"))
            } else { self.opaque_ptr.write_ptr(&value.opaque_ptr) }
        } else { Err(anyhow!("Not a pointer of a compatible type")) }
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
        if let Some((pointee_type_index, is_reference_type)) = self.metadata.pointer_pointee_type_index_and_is_reference() && !buffer.is_empty() &&
            self.metadata.namespace.can_assign_ptr_value(pointee_type_index, buffer[0].metadata.type_index) {
            let raw_ptr_array: Vec<OpaquePtr<M>> = buffer.iter().map(|x| {
                if x.is_nullptr() && is_reference_type {
                    Err(anyhow!("Cannot write value of nullptr to reference type"))
                } else { Ok(x.opaque_ptr.clone()) }
            }).collect::<anyhow::Result<Vec<OpaquePtr<M>>>>()?;
            self.opaque_ptr.write_ptr_array(raw_ptr_array.as_slice())
        } else { Err(anyhow!("Not a pointer of a compatible type")) }
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
