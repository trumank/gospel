use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock};
use anyhow::anyhow;
use gospel_typelib::type_model::{MutableTypeGraph, PrimitiveType, ResolvedUDTMemberLayout, Type, TypeLayoutCache, UserDefinedTypeMember};
use crate::memory_access::OpaquePtr;

#[derive(Clone)]
pub struct TypePtrMetadata {
    pub type_graph: Arc<RwLock<dyn MutableTypeGraph>>,
    pub layout_cache: Arc<RwLock<TypeLayoutCache>>,
    pub type_index: usize,
}
impl TypePtrMetadata {
    pub fn with_type_index(&self, type_index: usize) -> Self {
        Self{type_graph: self.type_graph.clone(), layout_cache: self.layout_cache.clone(), type_index}
    }
    pub fn size_and_alignment(&self) -> anyhow::Result<(usize, usize)> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        type_data.size_and_alignment(type_graph.deref(), layout_cache.deref_mut())
    }
    pub fn primitive_type_and_size(&self) -> anyhow::Result<Option<(PrimitiveType, usize)>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let layout_cache = self.layout_cache.read().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Primitive(primitive_type) = type_data {
            Ok(Some((primitive_type.clone(), primitive_type.size_and_alignment(&layout_cache.target_triplet)?)))
        } else { Ok(None) }
    }
    pub fn pointer_pointee_type_index(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::Pointer(pointer_type) = type_data {
            Ok(Some(pointer_type.pointee_type_index))
        } else { Ok(None) }
    }
    pub fn array_element_type_index(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Ok(Some(array_type.element_type_index))
        } else { Ok(None) }
    }
    pub fn array_static_array_length(&self) -> anyhow::Result<Option<usize>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        if let Type::Array(array_type) = type_graph.base_type_by_index(self.type_index) {
            Ok(Some(array_type.array_length))
        } else { Ok(None) }
    }
    pub fn struct_base_class_offset(&self, base_class_type_index: usize) -> anyhow::Result<Option<usize>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
        let type_data = type_graph.base_type_by_index(self.type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_base_class_offset(type_graph.base_type_index(base_class_type_index), type_graph.deref(), layout_cache.deref_mut())
        } else { Ok(None) }
    }
    pub fn struct_field_type_index_and_offset(&self, field_name: &str) -> anyhow::Result<Option<(usize, usize)>> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        let mut layout_cache = self.layout_cache.write().map_err(|x| anyhow!(x.to_string()))?;
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
    pub fn types_identical(&self, type_index_a: usize, type_index_b: usize) -> anyhow::Result<bool> {
        let type_graph = self.type_graph.read().map_err(|x| anyhow!(x.to_string()))?;
        Ok(type_graph.base_type_index(type_index_a) == type_graph.base_type_index(type_index_b))
    }
}

#[derive(Clone)]
pub struct DynamicPtr {
    pub opaque_ptr: OpaquePtr,
    pub metadata: TypePtrMetadata,
}
impl PartialEq for DynamicPtr {
    fn eq(&self, other: &Self) -> bool {
        self.opaque_ptr == other.opaque_ptr
    }
}
impl Eq for DynamicPtr {}
impl PartialOrd for DynamicPtr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.opaque_ptr.partial_cmp(&other.opaque_ptr)
    }
}
impl Ord for DynamicPtr {
    fn cmp(&self, other: &Self) -> Ordering {
        self.opaque_ptr.cmp(&other.opaque_ptr)
    }
}
impl Hash for DynamicPtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.opaque_ptr.hash(state)
    }
}
impl DynamicPtr {
    /// Offsets this pointer towards lower addresses by the given number of elements
    pub fn unchecked_offset_add(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self{opaque_ptr: self.opaque_ptr.clone() + (count * self.metadata.size_and_alignment()?.0), metadata: self.metadata.clone() })
    }
    /// Offsets this pointer towards higher addresses by the given number of elements
    pub fn unchecked_offset_sub(&self, count: usize) -> anyhow::Result<Self> {
        Ok(Self{opaque_ptr: self.opaque_ptr.clone() - (count * self.metadata.size_and_alignment()?.0), metadata: self.metadata.clone() })
    }
    /// Returns the pointer to the array element at the given index. Performs boundaries check
    pub fn get_array_element_ptr(&self, array_element_index: usize) -> anyhow::Result<Option<Self>> {
        if let Some(static_array_length) = self.metadata.array_static_array_length()? && array_element_index < static_array_length {
            Ok(Some(self.unchecked_offset_add(array_element_index)?))
        } else { Ok(None) }
    }
    /// Returns the pointer to the struct field with the given name
    pub fn get_struct_field_ptr(&self, field_name: &str) -> anyhow::Result<Option<Self>> {
        if let Some((field_type_index, field_offset)) = self.metadata.struct_field_type_index_and_offset(field_name)? {
            Ok(Some(Self{opaque_ptr: self.opaque_ptr.clone() + field_offset, metadata: self.metadata.with_type_index(field_type_index)}))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer as a pointer. Returns pointer to read value if this is a pointer, or empty option if it is not
    pub fn read_ptr(&self) -> anyhow::Result<Option<DynamicPtr>> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? {
            let pointee_opaque_ptr = self.opaque_ptr.read_ptr()?;
            Ok(Some(DynamicPtr{opaque_ptr: pointee_opaque_ptr, metadata: self.metadata.with_type_index(pointee_type_index)}))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn read_u8(&self) -> anyhow::Result<Option<u8>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 1 {
            Ok(Some(self.opaque_ptr.read_u8()?))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn read_u16(&self) -> anyhow::Result<Option<u16>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 2 {
            Ok(Some(self.opaque_ptr.read_u16()?))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn read_u32(&self) -> anyhow::Result<Option<u32>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 4 {
            Ok(Some(self.opaque_ptr.read_u32()?))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn read_u64(&self) -> anyhow::Result<Option<u64>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 8 {
            Ok(Some(self.opaque_ptr.read_u64()?))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive floating point value of the matching bit width
    pub fn read_f32(&self) -> anyhow::Result<Option<f32>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_floating_point() && primitive_size == 4 {
            Ok(Some(f32::from_bits(self.opaque_ptr.read_u32()?)))
        } else { Ok(None) }
    }
    /// Attempts to read this dynamic pointer value as a primitive integral value of the matching bit width and signedness
    pub fn read_f64(&self) -> anyhow::Result<Option<f64>> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_floating_point() && primitive_size == 8 {
            Ok(Some(f64::from_bits(self.opaque_ptr.read_u64()?)))
        } else { Ok(None) }
    }
    /// Utility functions to read signed primitive integral values of the matching bit width
    pub fn read_i8(&self) -> anyhow::Result<Option<i8>> { Ok(self.read_u8()?.map(|x| x as i8)) }
    pub fn read_i16(&self) -> anyhow::Result<Option<i16>> { Ok(self.read_u8()?.map(|x| x as i16)) }
    pub fn read_i32(&self) -> anyhow::Result<Option<i32>> { Ok(self.read_u8()?.map(|x| x as i32)) }
    pub fn read_i64(&self) -> anyhow::Result<Option<i64>> { Ok(self.read_u8()?.map(|x| x as i64)) }

    /// Attempts to write this dynamic pointer as a pointer
    pub fn write_ptr(&self, value: &DynamicPtr) -> anyhow::Result<()> {
        if let Some(pointee_type_index) = self.metadata.pointer_pointee_type_index()? && self.metadata.types_identical(pointee_type_index, value.metadata.type_index)? {
            self.opaque_ptr.write_ptr(&value.opaque_ptr)
        } else { Err(anyhow!("Not a pointer of a compatible type")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn write_u8(&self, value: u8) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 1 {
            self.opaque_ptr.write_u8(value)
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn write_u16(&self, value: u16) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 2 {
            self.opaque_ptr.write_u16(value)
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn write_u32(&self, value: u32) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 4 {
            self.opaque_ptr.write_u32(value)
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive integral value of the matching bit width
    pub fn write_u64(&self, value: u64) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_integral() && primitive_size == 8 {
            self.opaque_ptr.write_u64(value)
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive floating point value of the matching bit width
    pub fn write_f32(&self, value: f32) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_floating_point() && primitive_size == 4 {
            self.opaque_ptr.write_u32(value.to_bits())
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Attempts to write this dynamic pointer value as a primitive floating point value of the matching bit width
    pub fn write_f64(&self, value: f64) -> anyhow::Result<()> {
        if let Some((primitive_type, primitive_size)) = self.metadata.primitive_type_and_size()? && primitive_type.is_floating_point() && primitive_size == 8 {
            self.opaque_ptr.write_u64(value.to_bits())
        } else { Err(anyhow!("Not an integral type of the matching bit width")) }
    }
    /// Utility functions to write signed primitive integral values of the matching bit width
    pub fn write_i8(&self, value: i8) -> anyhow::Result<()> { self.write_u8(value as u8) }
    pub fn write_i16(&self, value: i16) -> anyhow::Result<()> { self.write_u16(value as u16) }
    pub fn write_i32(&self, value: i32) -> anyhow::Result<()> { self.write_u32(value as u32) }
    pub fn write_i64(&self, value: i64) -> anyhow::Result<()> { self.write_u64(value as u64) }
}
