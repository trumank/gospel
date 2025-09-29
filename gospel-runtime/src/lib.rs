#![feature(arbitrary_self_types)]
#![feature(ptr_as_ref_unchecked)]
#![feature(ptr_metadata)]
#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(min_specialization)]
#![feature(clone_to_uninit)]

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
macro_rules! gsb_codegen_implement_external_udt_field {
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
macro_rules! gsb_codegen_implement_local_udt_field {
    ($field_name:ident, $source_file_name:literal, $type_universe:ty, required, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        paste! {
            $(#[$field_attributes])*
            pub fn $field_name<'a>(&'a self) -> &'a $field_type {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_field_ref::<$field_type>(self, $source_file_name)
                    .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name))
            }
            $(#[$field_attributes])*
            pub fn [<$field_name _mut>]<'a>(&'a mut self) -> &'a mut $field_type {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_field_mut::<$field_type>(self, $source_file_name)
                    .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name))
            }
        }
    };
    ($field_name:ident, $source_file_name:literal, $type_universe:ty, optional, {$(#[$field_attributes:meta])*}, $field_type:ty) => {
        paste! {
            $(#[$field_attributes])*
            pub fn $field_name<'a>(&'a self) -> Option<&'a $field_type> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_field_ref::<$field_type>(self, $source_file_name)
            }
            $(#[$field_attributes])*
            pub fn [<$field_name _mut>]<'a>(&'a mut self) -> Option<&'a mut $field_type> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_field_mut::<$field_type>(self, $source_file_name)
            }
        }
    };
    ($field_name:ident, $source_file_name:literal, $type_universe:ty, required, {$(#[$field_attributes:meta])*}) => {
        paste! {
            $(#[$field_attributes])*
            pub fn $field_name<'a>(&'a self) -> gospel_runtime::local_type_model::DynRef<'a, $type_universe> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_dyn_ref(self, $source_file_name)
                    .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name))
            }
            $(#[$field_attributes])*
            pub fn [<$field_name _mut>]<'a>(&'a mut self) -> gospel_runtime::local_type_model::DynMut<'a, $type_universe> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_dyn_mut(self, $source_file_name)
                    .unwrap_or_else(|| panic!("Struct missing field: {}", $source_file_name))
            }
        }
    };
    ($field_name:ident, $source_file_name:literal, $type_universe:ty, optional, {$(#[$field_attributes:meta])*}) => {
        paste! {
            $(#[$field_attributes])*
            pub fn $field_name<'a>(&'a self) -> Option<gospel_runtime::local_type_model::DynRef<'a, $type_universe>> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_dyn_ref(self, $source_file_name)
            }
            $(#[$field_attributes])*
            pub fn [<$field_name _mut>]<'a>(&'a mut self) -> Option<gospel_runtime::local_type_model::DynMut<'a, $type_universe>> {
                use generic_statics::{define_namespace, Namespace};
                define_namespace!(FieldDescriptor);
                FieldDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeFieldTypeAndOffset<Self, $type_universe>>().get_dyn_mut(self, $source_file_name)
            }
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_external_enum_constant {
    ($constant_name:ident, $source_file_name:literal, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Self {
            use crate::gospel_runtime::core_type_definitions::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}", $source_file_name));
            Self::from_raw_discriminant(constant_raw_value)
        }
    };
    ($constant_name:ident, $source_file_name:literal, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<NS : gospel_runtime::external_type_model::TypeNamespace>(namespace: &NS) -> Option<Self> {
            use crate::gospel_runtime::core_type_definitions::StaticTypeTag;
            let enum_type_index = Self::store_type_descriptor_to_namespace(namespace);
            let constant_raw_value = namespace.type_layout_cache().lock().unwrap().get_enum_type_constant_value_cached(namespace.type_graph(), enum_type_index, $source_file_name)?;
            Some(Self::from_raw_discriminant(constant_raw_value))
        }
    };
}

#[macro_export]
macro_rules! gsb_codegen_implement_local_enum_constant {
    ($constant_name:ident, $source_file_name:literal, $type_universe:ty, sized, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name() -> Self {
            use generic_statics::{define_namespace, Namespace};
            define_namespace!(EnumConstantDescriptor);
            let constant_raw_value = EnumConstantDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeEnumConstant<Self, $type_universe>>().get_enum_constant_value(self, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}", $source_file_name));
            Self::sized_from_raw_discriminant(constant_raw_value)
        }
    };
    ($constant_name:ident, $source_file_name:literal, $type_universe:ty, sized, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name() -> Option<Self> {
            use generic_statics::{define_namespace, Namespace};
            define_namespace!(EnumConstantDescriptor);
            let constant_raw_value = EnumConstantDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeEnumConstant<Self, $type_universe>>().get_enum_constant_value(self, $source_file_name)?;
            Some(Self::sized_from_raw_discriminant(constant_raw_value))
        }
    };
    ($constant_name:ident, $source_file_name:literal, $type_universe:ty, boxed, required, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<A : std::alloc:::Allocator>(alloc: A) -> Box<Self, A> {
            use generic_statics::{define_namespace, Namespace};
            define_namespace!(EnumConstantDescriptor);
            let constant_raw_value = EnumConstantDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeEnumConstant<Self, $type_universe>>().get_enum_constant_value(self, $source_file_name)
                .unwrap_or_else(|| panic!("Enum missing constant: {}", $source_file_name));
            Self::boxed_from_raw_discriminant::<A>(constant_raw_value, alloc)
        }
    };
    ($constant_name:ident, $source_file_name:literal, $type_universe:ty, boxed, optional, {$(#[$field_attributes:meta])*}) => {
        $(#[$field_attributes])*
        pub fn $constant_name<A : std::alloc:::Allocator>(alloc: A) -> Option<Box<Self, A>> {
            use generic_statics::{define_namespace, Namespace};
            define_namespace!(EnumConstantDescriptor);
            let constant_raw_value = EnumConstantDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeEnumConstant<Self, $type_universe>>().get_enum_constant_value(self, $source_file_name)?;
            Some(Self::boxed_from_raw_discriminant::<A>(constant_raw_value, alloc))
        }
    };
}
