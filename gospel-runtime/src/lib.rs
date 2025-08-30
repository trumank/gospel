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
macro_rules! gsb_codegen_generate_type_struct {
    ($type_name:ident, $full_type_name:literal) => {
        #[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $type_name<M: gospel_runtime::memory_access::Memory> {
            inner_ptr: gospel_runtime::runtime_type_model::DynamicPtr<M>,
        }
        impl<M: gospel_runtime::memory_access::Memory> gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper<M> for $type_name<M> {
            fn from_ptr_unchecked(ptr: gospel_runtime::runtime_type_model::DynamicPtr<M>) -> Self {
                Self{inner_ptr: ptr}
            }
            fn get_inner_ptr(&self) -> &gospel_runtime::runtime_type_model::DynamicPtr<M> {
                &self.inner_ptr
            }
            fn can_typecast(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> anyhow::Result<bool> {
                if let Some(struct_name) = ptr_metadata.struct_type_name()? {
                    Ok(struct_name == $full_type_name)
                } else { Ok(false) }
            }
        }
    };
}
#[macro_export]
macro_rules! gsb_codegen_implement_field {
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required, $generated_field_type:ty) => {
        pub fn $field_name(&self) -> anyhow::Result<$generated_field_type> {
            let raw_field_ptr = self.inner_ptr.get_struct_field_ptr($source_file_name)?
                .ok_or_else(|| anyhow::anyhow!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name))?;
            use gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper;
            Ok(<$generated_field_type>::try_cast(&raw_field_ptr)?
                .ok_or_else(|| anyhow::anyhow!("Struct field is of incompatible type: {}:{}", stringify!($type_name), $source_file_name))?)
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional, $generated_field_type:ty) => {
        pub fn $field_name(&self) -> anyhow::Result<Option<$generated_field_type>> {
            if let Some(raw_field_ptr) = self.inner_ptr.get_struct_field_ptr($source_file_name)? {
                use gospel_runtime::static_type_wrappers::TypedDynamicPtrWrapper;
                Ok(Some(<$generated_field_type>::try_cast(&raw_field_ptr)?.ok_or_else(|| anyhow::anyhow!("Struct field is of incompatible type: {}:{}", stringify!($type_name), $source_file_name))?))
            } else { Ok(None) }
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, required) => {
        pub fn $field_name(&self) -> anyhow::Result<gospel_runtime::runtime_type_model::DynamicPtr<M>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name)?.ok_or_else(|| anyhow::anyhow!("Struct missing field: {}:{}", stringify!($type_name), $source_file_name))
        }
    };
    ($type_name:ty, $field_name:ident, $source_file_name:literal, optional) => {
        pub fn $field_name(&self) -> anyhow::Result<Option<gospel_runtime::runtime_type_model::DynamicPtr<M>>> {
            self.inner_ptr.get_struct_field_ptr($source_file_name)
        }
    };
}
#[macro_export]
macro_rules! gsb_codegen_implement_static_type {
    ($type_name:ident, $full_type_name:literal) => {
        impl<M: gospel_runtime::memory_access::Memory> gospel_runtime::static_type_wrappers::StaticallyTypedPtr<M> for $type_name<M> {
            fn store_type_descriptor(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> anyhow::Result<gospel_runtime::runtime_type_model::TypePtrMetadata> {
                let mut type_graph = namespace.type_graph.write().map_err(|x| anyhow::anyhow!(x.to_string()))?;
                let type_index = type_graph.find_create_named_udt_type($full_type_name)?.ok_or_else(|| anyhow::anyhow!("Named struct not found: {}", $full_type_name))?;
                Ok(gospel_runtime::runtime_type_model::TypePtrMetadata{namespace: namespace.clone(), type_index})
            }
        }
    };
}
