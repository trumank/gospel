#![feature(arbitrary_self_types)]
pub mod memory_access;
pub mod runtime_type_model;
pub mod current_process;
#[cfg(feature = "process")]
pub mod process;
#[cfg(feature = "minidump")]
pub mod minidump;
pub mod static_type_wrappers;
#[cfg(feature = "vm")]
pub mod vm_integration;

#[macro_export]
macro_rules! gsb_codegen_implement_field {
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, $type_name>) -> gospel_runtime::static_type_wrappers::Ref<M, $field_type> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).unwrap_or_else(|| panic!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name)).cast_ref_checked()
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, $type_name>) -> Option<gospel_runtime::static_type_wrappers::Ref<M, $field_type>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).map(|x| x.cast_ref_checked())
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, $type_name>) -> gospel_runtime::static_type_wrappers::Ref<M, ()> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).unwrap_or_else(|| panic!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name)).cast_ref_checked()
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, $type_name>) -> Option<gospel_runtime::static_type_wrappers::Ref<M, ()>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).map(|x| x.cast_ref_checked())
        }
    };
}
#[macro_export]
macro_rules! gsb_codegen_implement_type {
    ($type_name:ident, $full_type_name:literal, static_type) => {
        impl gospel_runtime::static_type_wrappers::StaticTypeTag for $type_name {
            fn store_type_descriptor(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> usize {
                let mut type_graph = namespace.type_graph.write().unwrap();
                type_graph.find_create_named_udt_type($full_type_name).unwrap().unwrap_or_else(|| panic!("Named struct not found: {}", $full_type_name))
            }
        }
        impl gospel_runtime::static_type_wrappers::DynamicTypeTag for $type_name {
            fn get_cast_target_type_descriptor(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> Option<usize> {
                use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
                Some(Self::store_type_descriptor(&ptr_metadata.namespace))
            }
        }
    };
    ($type_name:ident, $full_type_name:literal, dynamic_type) => {
        impl gospel_runtime::static_type_wrappers::DynamicTypeTag for $type_name {
            fn get_cast_target_type_descriptor(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> Option<usize> {
                if let Some(struct_type_name) = ptr_metadata.struct_type_name() && struct_type_name == $full_type_name {
                    // This pointer already represents the UDT we are casting to
                    Some(ptr_metadata.type_index)
                } else if let Some(base_class_indices) = ptr_metadata.struct_find_all_base_classes_by_type_name($full_type_name) && base_class_indices.len() == 1 {
                    // Only allow downcasting if there is only one base class type matching our type name (since we are a template, it is possible that we would have multiple)
                    Some(base_class_indices[0])
                } else { None }
            }
        }
    };
}
