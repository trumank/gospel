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
macro_rules! gsb_codegen_implement_udt_field {
    ($field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, Self>) -> gospel_runtime::static_type_wrappers::Ref<M, $field_type> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name)).cast_ref_checked()
        }
    };
    ($field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, Self>) -> Option<gospel_runtime::static_type_wrappers::Ref<M, $field_type>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).map(|x| x.cast_ref_checked())
        }
    };
    ($field_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, Self>) -> gospel_runtime::static_type_wrappers::Ref<M, ()> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name)).cast_ref_checked()
        }
    };
    ($field_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $field_name<M : gospel_runtime::memory_access::Memory>(self: &gospel_runtime::static_type_wrappers::Ref<M, Self>) -> Option<gospel_runtime::static_type_wrappers::Ref<M, ()>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name).map(|x| x.cast_ref_checked())
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_enum_type {
    ($type_name:ident, $full_type_name:literal, static_type) => {
        impl gospel_runtime::static_type_wrappers::StaticTypeTag for $type_name {
            fn store_type_descriptor(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> usize {
                let mut type_graph = namespace.type_graph.write().unwrap();
                type_graph.create_named_type($full_type_name, vec![]).unwrap().unwrap_or_else(|| panic!("Named enum type not found: {}", $full_type_name))
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
                if let Some(enum_type_name) = ptr_metadata.enum_type_name() && enum_type_name == $full_type_name {
                    Some(ptr_metadata.type_index)
                } else { None }
            }
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_enum_trivial_value {
    ($type_name:ident) => {
         impl gospel_runtime::static_type_wrappers::TrivialValue for $type_name {
            fn static_read<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>) -> anyhow::Result<Self> {
                Ok(Self(ptr.read_integral_type()?.unwrap_or_else(|| panic!("Failed to read: value is not compatible with enum {} underlying type", stringify!($type_name)))))
            }
            fn static_write<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, value: Self) -> anyhow::Result<()> {
                ptr.write_integral_type(ptr, value.0)
            }
            fn static_read_slice_unchecked<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut u64, buffer.len()) };
                if !ptr.read_integral_type_slice_unchecked(buffer)? {
                    panic!("Failed to read: value is not compatible with enum {} underlying type", stringify!($type_name));
                } else { Ok({}) }
            }
            fn static_write_slice_unchecked<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const u64, buffer.len()) };
                ptr.write_integral_type_slice_unchecked(underlying_type_buffer)
            }
        }
    };
    ($type_name:ident, $underlying_type:ty) => {
         impl gospel_runtime::static_type_wrappers::TrivialValue for $type_name {
            fn static_read<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>) -> anyhow::Result<Self> {
                Ok(Self(<$underlying_type>::static_read(ptr)?))
            }
            fn static_write<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, value: Self) -> anyhow::Result<()> {
                <$underlying_type>::static_write(ptr, value.0)
            }
            fn static_read_slice_unchecked<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut $underlying_type, buffer.len()) };
                <$underlying_type>::static_read_slice_unchecked(ptr, underlying_type_buffer)
            }
            fn static_write_slice_unchecked<M: gospel_runtime::memory_access::Memory>(ptr: &gospel_runtime::runtime_type_model::DynamicPtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                // This is safe as long as type has a transparent representation
                let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const $underlying_type, buffer.len()) };
                <$underlying_type>::static_write_slice_unchecked(ptr, underlying_type_buffer)
            }
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_enum_constant {
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, static_type, required, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> Self {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            use crate::gospel_runtime::static_type_wrappers::EnumUnderlyingType;
            let enum_type_index = Self::store_type_descriptor(&namespace);
            let constant_raw_value = namespace.get_enum_type_constant_value(enum_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(<$inner_type>::from_raw_discriminant(constant_raw_value))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, static_type, optional, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> Option<Self> {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            use crate::gospel_runtime::static_type_wrappers::EnumUnderlyingType;
            let enum_type_index = Self::store_type_descriptor(&namespace);
            let constant_raw_value = namespace.get_enum_type_constant_value(enum_type_index, $source_file_name)?;
            Some(Self(<$inner_type>::from_raw_discriminant(constant_raw_value)))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, dynamic_type, required, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadat) -> Self {
            use crate::gospel_runtime::static_type_wrappers::EnumUnderlyingType;
            let constant_raw_value = ptr_metadata.namespace.get_enum_type_constant_value(ptr_metadata.type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(<$inner_type>::from_raw_discriminant(constant_raw_value))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, dynamic_type, optional, {$(#[$field_attributes:meta])*}, $inner_type:ty) => {
        $(#[$field_attributes])*
        pub fn $constant_name(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadat) -> Option<Self> {
            use crate::gospel_runtime::static_type_wrappers::EnumUnderlyingType;
            let constant_raw_value = ptr_metadata.namespace.get_enum_type_constant_value(ptr_metadata.type_index, $source_file_name)?;
            Some(Self(<$inner_type>::from_raw_discriminant(constant_raw_value)))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, static_type, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> Self {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor(&namespace);
            let constant_raw_value = namespace.get_enum_type_constant_value(enum_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(constant_raw_value)
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, static_type, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> Option<Self> {
            use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor(&namespace);
            let constant_raw_value = namespace.get_enum_type_constant_value(enum_type_index, $source_file_name)?;
            Some(Self(constant_raw_value))
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, dynamic_type, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadat) -> Self {
            let constant_raw_value = ptr_metadata.namespace.get_enum_type_constant_value(ptr_metadata.type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}:{}", stringify!($type_name), $source_file_name));
            Self(constant_raw_value)
        }
    };
    ($type_name:ty, $constant_name:ident, $source_file_name:literal, dynamic_type, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadat) -> Option<Self> {
            let constant_raw_value = ptr_metadata.namespace.get_enum_type_constant_value(ptr_metadata.type_index, $source_file_name)?;
            Some(Self(constant_raw_value))
        }
    };
}
