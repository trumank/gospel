use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock};
use anyhow::anyhow;
use paste::paste;
use gospel_typelib::type_model::{MutableTypeGraph, PrimitiveType, ResolvedUDTMemberLayout, Type, TypeLayoutCache, UserDefinedTypeMember};
use crate::memory_access::{Memory, OpaquePtr};

/// Type ptr namespace represents a type hierarchy used by a hierarchy of related type pointers
#[derive(Clone)]
pub struct TypePtrNamespace {
    pub type_graph: Arc<RwLock<dyn MutableTypeGraph>>,
    pub layout_cache: Arc<RwLock<TypeLayoutCache>>,
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
    pub fn size_and_alignment(&self) -> anyhow::Result<(usize, usize)> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.namespace.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        type_data.size_and_alignment(type_graph.deref(), layout_cache.deref_mut())
    }
    pub fn primitive_type_and_size(&self) -> anyhow::Result<Option<(PrimitiveType, usize)>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let layout_cache = self.namespace.layout_cache.read().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Primitive(primitive_type) = type_data {
            Ok(Some((primitive_type.clone(), primitive_type.size_and_alignment(&layout_cache.target_triplet)?)))
        } else if let Type::Enum(enum_type) = type_data {
            let underlying_primitive_type = enum_type.underlying_type(&layout_cache.target_triplet)?;
            Ok(Some((underlying_primitive_type, underlying_primitive_type.size_and_alignment(&layout_cache.target_triplet)?)))
        } else { Ok(None) }
    }
    pub fn pointer_pointee_type_index(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Pointer(pointer_type) = type_data {
            Ok(Some(pointer_type.pointee_type_index))
        } else { Ok(None) }
    }
    pub fn array_element_type_index(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Ok(Some(array_type.element_type_index))
        } else { Ok(None) }
    }
    pub fn array_static_array_length(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Ok(Some(array_type.array_length))
        } else { Ok(None) }
    }
    pub fn struct_base_class_offset(&self, base_class_type_index: usize) -> anyhow::Result<Option<usize>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.namespace.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_base_class_offset(type_graph.base_type_index(base_class_type_index), type_graph.deref(), layout_cache.deref_mut())
        } else { Ok(None) }
    }
    pub fn struct_field_type_index_and_offset(&self, field_name: &str) -> anyhow::Result<Option<(usize, usize)>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.namespace.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_map_member_layout(field_name, &|context| {
                if let UserDefinedTypeMember::Field(field) = &context.owner_udt.members[context.member_index] &&
                    let ResolvedUDTMemberLayout::Field(field_layout) = &context.owner_layout.member_layouts[context.member_index] {
                    Some((field.member_type_index, context.owner_offset + field_layout.offset))
                } else { None }
            }, type_graph.deref(), layout_cache.deref_mut())
        } else { Ok(None) }
    }
    pub fn struct_type_name(&self) -> anyhow::Result<Option<String>> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            Ok(user_defined_type.name.clone())
        } else { Ok(None) }
    }
    pub fn are_types_compatible(&self, type_index_a: usize, type_index_b: usize) -> anyhow::Result<bool> {
        let type_graph = self.namespace.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        // TODO: This should be relaxed to allow integral conversions between integers of the same width
        Ok(type_graph.base_type_index(type_index_a) == type_graph.base_type_index(type_index_b))
    }
}

macro_rules! implement_dynamic_ptr_numeric_access {
    ($data_type: ident, $is_integral: literal, $is_floating_point: literal) => {
        paste! {
            pub fn [<read_ $data_type>](&self) -> anyhow::Result<Option<$data_type>> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    Ok(Some(self.opaque_ptr.[<read_ $data_type>]()?))
                } else { Ok(None) }
            }
            pub fn [<read_ $data_type _slice_unchecked>](&self, buffer: &mut [$data_type]) -> anyhow::Result<bool> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    self.opaque_ptr.[<read_ $data_type _array>](buffer)?;
                    Ok(true)
                } else { Ok(false) }
            }
            pub fn [<write_ $data_type>](&self, value: $data_type) -> anyhow::Result<()> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
                    self.opaque_ptr.[<write_ $data_type>](value)
                } else { Err(anyhow!("Not an integral type of the matching bit width")) }
            }
            pub fn [<write_ $data_type _slice_unchecked>](&self, buffer: &[$data_type]) -> anyhow::Result<()> {
                if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() == $is_integral && primitive_type.is_floating_point() == $is_floating_point && primitive_size == size_of::<$data_type>() {
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
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn add_unchecked(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self{opaque_ptr: self.opaque_ptr.clone() + (count * self.metadata.size_and_alignment()?.0), metadata: self.metadata.clone() })
    }
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn sub_unchecked(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self{opaque_ptr: self.opaque_ptr.clone() - (count * self.metadata.size_and_alignment()?.0), metadata: self.metadata.clone() })
    }
    /// Returns the pointer to the array element at the given index. Performs boundaries check
    pub fn get_array_element_ptr(&self, array_element_index: usize) -> anyhow::Result<Option<Self>> {
        if let Some(static_array_length) = self.metadata.array_static_array_length()? && array_element_index < static_array_length {
            Ok(Some(self.add_unchecked(array_element_index)?))
        } else { Ok(None) }
    }
    /// Returns the pointer to the struct field with the given name
    pub fn get_struct_field_ptr(&self, field_name: &str) -> anyhow::Result<Option<Self>> {
        if let Some((field_type_index, field_offset)) = self.metadata.struct_field_type_index_and_offset(field_name)? {
            Ok(Some(Self{opaque_ptr: self.opaque_ptr.clone() + field_offset, metadata: self.metadata.with_type_index(field_type_index)}))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer as a pointer
    pub fn read_ptr(&self) -> anyhow::Result<Option<Self>> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? {
            let pointee_opaque_ptr = self.opaque_ptr.read_ptr()?;
            Ok(Some(Self{opaque_ptr: pointee_opaque_ptr, metadata: self.metadata.with_type_index(pointee_type_index)}))
        } else { Ok(None) }
    }
    pub fn read_ptr_slice_unchecked(&self, len: usize) -> anyhow::Result<Option<Vec<Self>>> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? {
            let element_metadata = self.metadata.with_type_index(pointee_type_index);
            Ok(Some(self.opaque_ptr.read_ptr_array(len)?.into_iter().map(|x| Self{opaque_ptr: x, metadata: element_metadata.clone()}).collect()))
        } else { Ok(None) }
    }
    /// Attempts to write this dynamic pointer as a pointer
    pub fn write_ptr(&self, value: &Self) -> anyhow::Result<()> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? && self.metadata.are_types_compatible(pointee_type_index, value.metadata.type_index)? {
            self.opaque_ptr.write_ptr(&value.opaque_ptr)
        } else { Err(anyhow!("Not a pointer of a compatible type")) }
    }
    pub fn write_ptr_slice_unchecked(&self, buffer: &[Self]) -> anyhow::Result<()> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? && !buffer.is_empty() && self.metadata.are_types_compatible(pointee_type_index, buffer[0].metadata.type_index)? {
            let raw_ptr_array: Vec<OpaquePtr<M>> = buffer.iter().map(|x| x.opaque_ptr.clone()).collect();
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
