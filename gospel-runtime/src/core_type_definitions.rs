use std::collections::HashMap;
use std::hash::{Hash};
use std::ops::{Deref, DerefMut};
use std::sync::{Mutex, RwLock};
use gospel_typelib::type_model::{calculate_static_cast_pointer_adjust, MutableTypeGraph, PrimitiveType, ResolvedUDTMemberLayout, TargetTriplet, Type, TypeLayoutCache, UserDefinedTypeMember};
use crate::local_type_model::{native_target_triplet, TypeUniverse};

/// Maps to the char8_t in C++ that has the size of 8 bits on all target triplets
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Char8(pub u8);
/// Maps to the char16_t in C++ that has the size of 16 bits on all target triplets
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Char16(pub u16);
/// Maps to the char32_t in C++ that has the size of 32 bits on all target triplets
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Char32(pub u32);

/// Used as a trait bound to allow passing non-type bool parameters as template instantiation arguments to bindings-generated types
pub trait BoolValueTypeTag : IntegralValueTypeTag {}

/// Used as a trait bound to allow passing non-type integral type parameters as template instantiation arguments to bindings-generated types
pub trait IntegralValueTypeTag { fn get_raw_integral_value() -> u64; }

/// Type used to represent "true" value on generic wrapped types
pub enum TrueType {}
impl IntegralValueTypeTag for TrueType { fn get_raw_integral_value() -> u64 { 0 } }
impl BoolValueTypeTag for TrueType {}

/// Type used to represent "false" value on generic wrapped types
pub enum FalseType {}
impl IntegralValueTypeTag for FalseType { fn get_raw_integral_value() -> u64 { 1 } }
impl BoolValueTypeTag for FalseType {}


/// Used as a key to hash lookups for the calculation of various forms of layout
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct FastTypeLayoutCacheKey {
    type_index: usize,
    name_address: usize,
}

/// Wrapper around type layout cache that allows caching more information using static lifetime strings as keys
pub struct StaticTypeLayoutCache {
    pub layout_cache: TypeLayoutCache,
    field_layout_cache: HashMap<FastTypeLayoutCacheKey, Option<(usize, usize)>>,
    enum_constant_cache: HashMap<FastTypeLayoutCacheKey, Option<u64>>,
    static_type_cache: HashMap<usize, Option<usize>>,
    static_cast_cache: HashMap<(usize, usize), Option<i64>>,
}
impl StaticTypeLayoutCache {
    /// Creates a new type layout cache from the given type graph
    pub fn create(target_triplet: TargetTriplet) -> StaticTypeLayoutCache {
        StaticTypeLayoutCache{ layout_cache: TypeLayoutCache::create(target_triplet), field_layout_cache: HashMap::default(),
            enum_constant_cache: HashMap::default(), static_type_cache: HashMap::default(), static_cast_cache: HashMap::default() }
    }
    /// This function answers the question "by how much do I need to offset pointer to type from_index to get a pointer to type to_index?"
    pub fn get_static_cast_pointer_adjust(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, from_type_index: usize, to_type_index: usize) -> Option<i64> {
        let cache_key = (from_type_index, to_type_index);
        if let Some(existing_pointer_adjust) = self.static_cast_cache.get(&cache_key) {
            existing_pointer_adjust.clone()
        } else {
            let new_pointer_adjust = calculate_static_cast_pointer_adjust(type_graph.write().unwrap().deref_mut(), &mut self.layout_cache, from_type_index, to_type_index);
            self.static_cast_cache.insert(cache_key, new_pointer_adjust.clone());
            new_pointer_adjust
        }
    }
    /// Reads the value of the enum constant with the given name at specified enum type index, and returns it
    pub fn get_enum_type_constant_value(&self, type_graph: &RwLock<dyn MutableTypeGraph>, enum_type_index: usize, constant_name: &str) -> Option<u64> {
        let type_graph = type_graph.read().unwrap();
        if let Type::Enum(enum_type) = type_graph.base_type_by_index(enum_type_index) {
            if let Some(constant) = enum_type.constants.iter().find(|x| x.name.as_ref().map(|y| y.as_ref()) == Some(constant_name)) {
                Some(enum_type.constant_value(constant, &self.layout_cache.target_triplet).unwrap())
            } else { None }
        } else { None }
    }
    pub fn get_enum_type_constant_value_cached(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, enum_type_index: usize, constant_name: &'static str) -> Option<u64> {
        let cache_key = FastTypeLayoutCacheKey{type_index: enum_type_index, name_address: constant_name.as_ptr().addr()};
        if let Some(existing_constant_value) = self.enum_constant_cache.get(&cache_key) {
            existing_constant_value.clone()
        } else {
            let enum_constant_value = self.get_enum_type_constant_value(type_graph, enum_type_index, constant_name);
            self.enum_constant_cache.insert(cache_key, enum_constant_value.clone());
            enum_constant_value
        }
    }
    pub fn get_static_type_index_cached(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, full_type_name: &'static str) -> Option<usize> {
        let cache_key = full_type_name.as_ptr().addr();
        if let Some(existing_static_type_index) = self.static_type_cache.get(&cache_key) {
            existing_static_type_index.clone()
        } else {
            let mut writeable_type_graph = type_graph.write().unwrap();
            let new_type_index = writeable_type_graph.create_named_type(full_type_name, vec![]).unwrap();
            self.static_type_cache.insert(cache_key, new_type_index.clone());
            new_type_index
        }
    }
    pub fn get_struct_field_type_index_and_offset(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, type_index: usize, field_name: &str) -> Option<(usize, usize)> {
        let readable_type_graph = type_graph.read().unwrap();
        let base_type_index = readable_type_graph.base_type_index(type_index);
        let type_data = readable_type_graph.type_by_index(base_type_index);
        if let Type::UDT(user_defined_type) = type_data {
            user_defined_type.find_map_member_layout(base_type_index, field_name, &|context| {
                if let UserDefinedTypeMember::Field(field) = &context.owner_udt.members[context.member_index] &&
                    let ResolvedUDTMemberLayout::Field(field_layout) = &context.owner_layout.member_layouts[context.member_index] {
                    Some((field.member_type_index, context.owner_offset + field_layout.offset))
                } else { None }
            }, readable_type_graph.deref(), &mut self.layout_cache).unwrap()
        } else { None }
    }
    pub fn get_struct_field_type_index_and_offset_cached(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, type_index: usize, field_name: &'static str) -> Option<(usize, usize)> {
        let layout_cache = FastTypeLayoutCacheKey{type_index, name_address: field_name.as_ptr().addr(), };
        if let Some(existing_layout) = self.field_layout_cache.get(&layout_cache) {
            existing_layout.clone()
        } else {
            let field_layout = self.get_struct_field_type_index_and_offset(type_graph, type_index, field_name);
            self.field_layout_cache.insert(layout_cache, field_layout.clone());
            field_layout
        }
    }
    /// Calculates size and alignment of the type at given index, or returns the value from cache if it has been calculated previously
    pub fn get_type_size_and_alignment_cached(&mut self, type_graph: &RwLock<dyn MutableTypeGraph>, type_index: usize) -> (usize, usize) {
        let readable_type_graph = type_graph.read().unwrap();
        let base_type_index = readable_type_graph.base_type_index(type_index);
        Type::size_and_alignment(base_type_index, type_graph.read().unwrap().deref(), &mut self.layout_cache).unwrap()
    }
}

/// Implemented on the types that have identity and can be represented in a type namespace
pub trait StaticTypeTag {
    /// Stores type descriptor for this type in the given type graph and returns its index
    fn store_type_descriptor_to_namespace<T : TypeNamespace>(namespace: &T) -> usize {
        let target_triplet = namespace.type_target_triplet();
        let type_graph = namespace.type_graph();
        let type_cache = namespace.type_layout_cache();
        Self::store_type_descriptor_raw(type_graph, target_triplet, type_cache)
    }
    /// Stores type descriptor for this type in the given type graph and returns its index
    fn store_type_descriptor_to_universe<T: TypeUniverse>() -> usize {
        let target_triplet = native_target_triplet();
        let type_graph = T::type_graph();
        let type_cache = T::type_layout_cache();
        Self::store_type_descriptor_raw(type_graph, target_triplet, type_cache)
    }
    /// Stores type descriptor for this type in the given type graph and returns its index
    fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, target_triplet: TargetTriplet, type_cache: &Mutex<StaticTypeLayoutCache>) -> usize;
}

macro_rules! implement_primitive_type_tag {
    ($value_type:ty, $primitive_type:expr) => {
       impl StaticTypeTag for $value_type {
            fn store_type_descriptor_raw(type_graph: &RwLock<dyn MutableTypeGraph>, _target_triplet: TargetTriplet, _type_cache: &Mutex<StaticTypeLayoutCache>) -> usize {
                type_graph.write().unwrap().store_type(Type::Primitive($primitive_type))
            }
       }
    }
}
pub(crate) use implement_primitive_type_tag;
use crate::external_type_model::TypeNamespace;

// Implement type tag for rust primitive types with well-known size across all platforms
implement_primitive_type_tag!(u8, PrimitiveType::UnsignedChar);
implement_primitive_type_tag!(u16, PrimitiveType::UnsignedShortInt);
implement_primitive_type_tag!(u32, PrimitiveType::UnsignedInt);
implement_primitive_type_tag!(u64, PrimitiveType::UnsignedLongLongInt);
implement_primitive_type_tag!(i8, PrimitiveType::Char);
implement_primitive_type_tag!(i16, PrimitiveType::ShortInt);
implement_primitive_type_tag!(i32, PrimitiveType::Int);
implement_primitive_type_tag!(i64, PrimitiveType::LongLongInt);
implement_primitive_type_tag!(f32, PrimitiveType::Float);
implement_primitive_type_tag!(f64, PrimitiveType::Double);
implement_primitive_type_tag!(bool, PrimitiveType::Bool);

// Implement type tag for type wrappers with well-known size across all platforms
implement_primitive_type_tag!(Char8, PrimitiveType::Char8);
implement_primitive_type_tag!(Char16, PrimitiveType::Char16);
implement_primitive_type_tag!(Char32, PrimitiveType::Char32);

// Void type is sizeless on all platforms and is equivalent to rust Unit type
implement_primitive_type_tag!((), PrimitiveType::Void);
