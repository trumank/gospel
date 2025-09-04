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
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}, $generated_field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name(&self) -> $generated_field_type {
            let raw_field_ptr = self.inner_ptr.get_struct_field_ptr($source_file_name)
                .unwrap_or_else(|| panic!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name));
            use gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper;
            <$generated_field_type>::do_static_cast(&raw_field_ptr)
                .unwrap_or_else(|| panic!("Struct field is of incompatible type: {}:{}", stringify!($type_name), $source_file_name))
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}, $generated_field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name(&self) -> Option<$generated_field_type> {
            if let Some(raw_field_ptr) = self.inner_ptr.get_struct_field_ptr($source_file_name) {
                use gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper;
                Some(<$generated_field_type>::do_static_cast(&raw_field_ptr).unwrap_or_else(|| panic!("Struct field is of incompatible type: {}:{}", stringify!($type_name), $source_file_name)))
            } else { None }
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name(&self) -> gospel_runtime::runtime_type_model::DynamicPtr<M> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).unwrap_or_else(|| panic!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name))
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name(&self) -> Option<gospel_runtime::runtime_type_model::DynamicPtr<M>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name)
        }
    };
}
#[macro_export]
macro_rules! gsb_codegen_implement_type {
    ($type_name:ident, $full_type_name:literal, static_type) => {
        impl<M: gospel_runtime::memory_access::Memory> gospel_runtime::static_type_wrappers::StaticallyTypedPtr<M> for $type_name<M> {
            fn store_type_descriptor(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> usize {
                let mut type_graph = namespace.type_graph.write().unwrap();
                let type_index = type_graph.find_create_named_udt_type($full_type_name).unwrap().unwrap_or_else(|| panic!("Named struct not found: {}", $full_type_name));
                type_index
            }
        }
        impl<M: gospel_runtime::memory_access::Memory> gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper<M> for $type_name<M> {
            fn from_ptr_unchecked(ptr: gospel_runtime::runtime_type_model::DynamicPtr<M>) -> Self {
                Self{inner_ptr: ptr}
            }
            fn get_inner_ptr(&self) -> &gospel_runtime::runtime_type_model::DynamicPtr<M> {
                &self.inner_ptr
            }
            fn is_pointee_type_compatible(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> bool {
                use crate::gospel_runtime::static_type_wrappers::StaticallyTypedPtr;
                let struct_type_index = Self::store_type_descriptor(&ptr_metadata.namespace);
                // Just being able to downcast or upcast is not enough here, the invariant of is_pointee_type_compatible is that it should be done without changing the pointer address
                ptr_metadata.base_type_index() == struct_type_index ||
                    ptr_metadata.struct_get_upcast_this_add_adjust(struct_type_index) == Some(0) ||
                    ptr_metadata.struct_get_unchecked_downcast_this_sub_adjust(struct_type_index) == Some(0)
            }
            fn do_static_cast(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>) -> Option<Self> {
                use crate::gospel_runtime::static_type_wrappers::StaticallyTypedPtr;
                let struct_type_index = Self::store_type_descriptor(&ptr.metadata.namespace);
                if ptr.metadata.base_type_index() == struct_type_index {
                    Some(Self::from_ptr_unchecked(ptr.clone()))
                } else if let Some(upcast_this_adjust) = ptr.metadata.struct_get_upcast_this_add_adjust(struct_type_index) {
                    let metadata = ptr.metadata.with_type_index_and_cv_qualifiers(struct_type_index);
                    Some(Self::from_ptr_unchecked(gospel_runtime::runtime_type_model::DynamicPtr{opaque_ptr: ptr.opaque_ptr.clone() + upcast_this_adjust, metadata}))
                } else if let Some(downcast_this_adjust) = ptr.metadata.struct_get_unchecked_downcast_this_sub_adjust(struct_type_index) {
                    let metadata = ptr.metadata.with_type_index_and_cv_qualifiers(struct_type_index);
                    Some(Self::from_ptr_unchecked(gospel_runtime::runtime_type_model::DynamicPtr{opaque_ptr: ptr.opaque_ptr.clone() - downcast_this_adjust, metadata}))
                } else {
                    None
                }
            }
        }
    };
    ($type_name:ident, $full_type_name:literal, dynamic_type) => {
        impl<M: gospel_runtime::memory_access::Memory> gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper<M> for $type_name<M> {
            fn from_ptr_unchecked(ptr: gospel_runtime::runtime_type_model::DynamicPtr<M>) -> Self {
                Self{inner_ptr: ptr}
            }
            fn get_inner_ptr(&self) -> &gospel_runtime::runtime_type_model::DynamicPtr<M> {
                &self.inner_ptr
            }
            fn is_pointee_type_compatible(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> bool {
                // Only allow downcasting if there is only one base class type matching our type name (since we are a template, it is possible that we would have multiple)
                // Just being able to upcast is not enough here, the invariant of is_pointee_type_compatible is that it should be done without changing the pointer address
                if let Some(struct_type_name) = ptr_metadata.struct_type_name() && struct_type_name == $full_type_name {
                    true
                } else if let Some(base_class_indices) = ptr_metadata.struct_find_all_base_classes_by_type_name($full_type_name) && base_class_indices.len() == 1 &&
                    ptr_metadata.struct_get_upcast_this_add_adjust(base_class_indices[0]) == Some(0) {
                    true
                } else { false }
            }
            fn do_static_cast(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>) -> Option<Self> {
                // Only allow downcasting if there is only one base class type matching our type name (since we are a template, it is possible that we would have multiple)
                if let Some(struct_type_name) = ptr.metadata.struct_type_name() && struct_type_name == $full_type_name {
                    Some(Self::from_ptr_unchecked(ptr.clone()))
                } else if let Some(base_class_indices) = ptr.metadata.struct_find_all_base_classes_by_type_name($full_type_name) && base_class_indices.len() == 1 &&
                    let Some(upcast_this_adjust) = ptr.metadata.struct_get_upcast_this_add_adjust(base_class_indices[0]) {
                    let metadata = ptr.metadata.with_type_index_and_cv_qualifiers(base_class_indices[0]);
                    Some(Self::from_ptr_unchecked(gospel_runtime::runtime_type_model::DynamicPtr{opaque_ptr: ptr.opaque_ptr.clone() + upcast_this_adjust, metadata}))
                } else { None }
            }
        }
    };
}
