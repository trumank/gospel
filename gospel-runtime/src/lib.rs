#![feature(arbitrary_self_types)]
#![feature(ptr_as_ref_unchecked)]
#![feature(ptr_metadata)]
#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(min_specialization)]

pub mod core_type_definitions;
#[cfg(feature = "external")]
pub mod external_memory;
#[cfg(feature = "external")]
pub mod external_type_model;
#[cfg(feature = "external")]
pub mod current_process;
#[cfg(feature = "process")]
pub mod process;
#[cfg(feature = "minidump")]
pub mod minidump;
#[cfg(feature = "local")]
pub mod local_type_model;
#[cfg(feature = "vm")]
pub mod vm_integration;

#[macro_export]
macro_rules! gsb_codegen_implement_udt_field {
    ($field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(self: &gospel_runtime::external_type_model::Ref<M, Self>) -> gospel_runtime::external_type_model::Ref<M, $field_type> {
            use gospel_runtime::core_type_definitions::StaticTypeTag;
            use std::ops::Deref;
            use std::ops::Add;
            let static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
            let (_, field_offset_bytes) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(self.inner_ptr.memory.type_graph(), static_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name));
            gospel_runtime::external_type_model::Ref::from_raw_ptr(self.inner_ptr.clone().add(field_offset_bytes))
        }
    };
    ($field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(self: &gospel_runtime::external_type_model::Ref<M, Self>) -> Option<gospel_runtime::external_type_model::Ref<M, $field_type>> {
            use gospel_runtime::core_type_definitions::StaticTypeTag;
            use std::ops::Deref;
            use std::ops::Add;
            let static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
            let (_, field_offset_bytes) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(self.inner_ptr.memory.type_graph(), static_type_index, $source_file_name)?;
            Some(gospel_runtime::external_type_model::Ref::from_raw_ptr(self.inner_ptr.clone().add(field_offset_bytes)))
        }
    };
    ($field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(self: &gospel_runtime::external_type_model::Ref<M, Self>) -> gospel_runtime::external_type_model::DynPtr<M> {
            use gospel_runtime::core_type_definitions::StaticTypeTag;
            use std::ops::Deref;
            use std::ops::Add;
            let static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
            let (field_type_index, field_offset_bytes) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(self.inner_ptr.memory.type_graph(), static_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name));
            gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone().add(field_offset_bytes), field_type_index)
        }
    };
    ($field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(self: &gospel_runtime::external_type_model::Ref<M, Self>) -> Option<gospel_runtime::external_type_model::DynPtr<M>> {
            use gospel_runtime::core_type_definitions::StaticTypeTag;
            use std::ops::Deref;
            use std::ops::Add;
            let static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
            let (field_type_index, field_offset_bytes) = self.inner_ptr.memory.type_layout_cache().lock().unwrap().get_struct_field_type_index_and_offset_cached(self.inner_ptr.memory.type_graph(), static_type_index, $source_file_name)?;
            Some(gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone().add(field_offset_bytes), field_type_index))
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_enum_trivial_value {
    ($type_name:ident) => {
         impl gospel_runtime::external_type_model::ExternallyConvertible for $type_name {
            fn read_external<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>) -> anyhow::Result<Self> {
                use gospel_runtime::core_type_definitions::StaticTypeTag;
                let enum_static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
                let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone(), enum_static_type_index);
                Ok(Self(enum_dyn_ptr.read_integral_type()?))
            }
            fn write_external<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                use gospel_runtime::core_type_definitions::StaticTypeTag;
                let enum_static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
                let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone(), enum_static_type_index);
                enum_dyn_ptr.write_integral_type(ptr, value.0)
            }
            fn read_external_slice<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                use gospel_runtime::core_type_definitions::StaticTypeTag;
                let enum_static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
                let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone(), enum_static_type_index);
                // This is safe as long as type has a transparent representation
                let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut u64, buffer.len()) };
                enum_dyn_ptr.read_integral_type_slice(buffer)
            }
            fn write_external_slice<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                use gospel_runtime::core_type_definitions::StaticTypeTag;
                let enum_static_type_index = Self::store_type_descriptor_to_namespace(self.inner_ptr.memory.deref());
                let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(self.inner_ptr.clone(), enum_static_type_index);
                // This is safe as long as type has a transparent representation
                let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const u64, buffer.len()) };
                enum_dyn_ptr.write_integral_type_slice(underlying_type_buffer)
            }
        }
    };
    ($type_name:ident, $underlying_type:ty) => {
         impl gospel_runtime::external_type_model::ExternallyConvertible for $type_name {
            fn read_external<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>) -> anyhow::Result<Self> {
                Ok(Self(<$underlying_type>::read_external(ptr)?))
            }
            fn write_external<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                <$underlying_type>::write_external(ptr, value.0)
            }
            fn read_external_slice<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut $underlying_type, buffer.len()) };
                <$underlying_type>::read_external_slice(ptr, underlying_type_buffer)
            }
            fn write_external_slice<M: gospel_runtime::external_memory::Memory>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const $underlying_type, buffer.len()) };
                <$underlying_type>::write_external_slice(ptr, underlying_type_buffer)
            }
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_enum_constant {
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Self {
            use crate::gospel_runtime::core_type_definitions::StaticTypeTag;
            use crate::gospel_runtime::external_type_model::EnumUnderlyingType;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(<$inner_type>::from_raw_discriminant(constant_raw_value))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Option<Self> {
            use crate::gospel_runtime::core_type_definitions::StaticTypeTag;
            use crate::gospel_runtime::external_type_model::EnumUnderlyingType;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)?;
            Some(Self(<$inner_type>::from_raw_discriminant(constant_raw_value)))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Self {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(constant_raw_value)
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Option<Self> {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)?;
            Some(Self(constant_raw_value))
        }
    };
}
