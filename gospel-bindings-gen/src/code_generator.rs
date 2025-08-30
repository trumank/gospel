use crate::module_processor::ResolvedBindingsModuleContext;
use anyhow::{anyhow, bail};
use gospel_typelib::type_model::{PrimitiveType, Type, TypeGraphLike, UserDefinedTypeMember};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::collections::{HashMap, HashSet};
use convert_case::{Case, Casing};
use syn::{parse2, parse_str, File};
use gospel_vm::vm::GospelVMClosure;

#[derive(Debug)]
pub(crate) struct CodeGenerationContext {
    pub(crate) module_context: ResolvedBindingsModuleContext,
    pub(crate) bindings_mod_name: String,
}
impl CodeGenerationContext {
    fn generate_primitive_type(primitive_type: &PrimitiveType) -> Option<TokenStream> {
        match primitive_type {
            PrimitiveType::Void => None,
            PrimitiveType::Char => Some(quote!{ i8 }),
            PrimitiveType::UnsignedChar => Some(quote!{ u8 }),
            PrimitiveType::WideChar => Some(quote! { gospel_runtime::static_type_wrappers::WideChar }),
            PrimitiveType::ShortInt => Some(quote!{ i16 }),
            PrimitiveType::UnsignedShortInt => Some(quote!{ u16 }),
            PrimitiveType::Int => Some(quote!{ i32 }),
            PrimitiveType::UnsignedInt => Some(quote!{ u32 }),
            PrimitiveType::Float => Some(quote!{ f32 }),
            PrimitiveType::Double => Some(quote!{ f64 }),
            PrimitiveType::Bool => Some(quote!{ bool }),
            PrimitiveType::LongInt => Some(quote! { gospel_runtime::static_type_wrappers::LongInt }),
            PrimitiveType::UnsignedLongInt => Some(quote! { gospel_runtime::static_type_wrappers::UnsignedLongInt }),
            PrimitiveType::LongLongInt => Some(quote!{ i64 }),
            PrimitiveType::UnsignedLongLongInt => Some(quote!{ u64 }),
            PrimitiveType::Char8 => Some(quote!{ u8 }),
            PrimitiveType::Char16 => Some(quote!{ u16 }),
            PrimitiveType::Char32 => Some(quote!{ u32 }),
        }
    }
    fn generate_short_udt_name(type_name: &str) -> String {
        if let Some(last_separator_index) = type_name.rfind('$') {
            type_name[(last_separator_index + 1)..].to_string()
        } else { type_name.to_string() }
    }
    fn convert_field_name_to_snake_case(field_name: &str) -> String {
        let converted_name = field_name.from_case(Case::UpperCamel).to_case(Case::Snake);
        if parse_str::<Ident>(&converted_name).is_ok() { converted_name } else { format!("r_{}", converted_name) }
    }
    fn generate_type_qualified_name(&self, source_crate_name: &Option<String>, type_name: &str) -> TokenStream {
        let crate_name = Ident::new(source_crate_name.as_ref().map(|x| x.as_str()).unwrap_or("crate"), Span::call_site());
        let short_type_name = Ident::new(&Self::generate_short_udt_name(type_name), Span::call_site());
        let mod_name = Ident::new(&self.bindings_mod_name, Span::call_site());
        quote! { #crate_name::#mod_name::#short_type_name }
    }
    fn generate_doc_comment(function_closure: &Option<GospelVMClosure>, doc_metadata: &str) -> Option<TokenStream> {
        let documentation_attributes: Vec<TokenStream> = function_closure.as_ref()
            .and_then(|x| x.function_metadata(doc_metadata)).into_iter()
            .flat_map(|x| x.lines())
            .filter(|x| !x.is_empty())
            .map(|doc_comment_line| quote! { #[doc = #doc_comment_line] })
            .collect();
        if documentation_attributes.is_empty() { None } else { Some(quote!{ #(#documentation_attributes)* }) }
    }
    fn generate_type_reference(&self, type_index: usize) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);

        match type_definition {
            Type::Array(array_type) => {
                let pointee_type = self.generate_type_reference(array_type.element_type_index)?;
                Ok(quote! {gospel_runtime::static_type_wrappers::StaticArrayPtr::<M, #pointee_type>})
            },
            Type::Pointer(pointer_type) => {
                let pointee_type = self.generate_type_reference(pointer_type.pointee_type_index)?;
                if pointer_type.is_reference {
                    Ok(quote! {gospel_runtime::static_type_wrappers::IndirectRef::<M, #pointee_type>})
                } else {
                    Ok(quote! {gospel_runtime::static_type_wrappers::IndirectPtr::<M, #pointee_type>})
                }
            }
            Type::CVQualified(cv_qualified_type) => {
                self.generate_type_reference(cv_qualified_type.base_type_index)
            }
            Type::Primitive(primitive_type) => {
                if let Some(primitive_inner_type) = Self::generate_primitive_type(primitive_type) {
                    Ok(quote! {gospel_runtime::static_type_wrappers::TrivialPtr::<M, #primitive_inner_type>})
                } else {
                    Ok(quote! { gospel_runtime::static_type_wrappers::VoidPtr::<M> })
                }
            }
            Type::Function(_) => {
                // TODO: Implement function pointer static type wrapper and related code generation (will likely need unique type per function signature)
                Ok(quote! { gospel_runtime::static_type_wrappers::VoidPtr::<M> })
            }
            Type::UDT(user_defined_type) => {
                // TODO: We could generate more accurate bindings based not just on the name of the type but also on the template parameters
                if let Some(udt_name) = &user_defined_type.name && let Some(source_crate_name) = self.module_context.type_name_to_dependency_crate_name.get(udt_name) {
                    let full_type_name = self.generate_type_qualified_name(source_crate_name, udt_name);
                    Ok(quote! { #full_type_name::<M> })
                } else {
                    Ok(quote! { gospel_runtime::static_type_wrappers::VoidPtr::<M> })
                }
            }
            Type::Enum(enum_type) => {
                // Check if this enum type has a statically known underlying type that does not depend on the target or the full list of constants
                // If it does, we can generate the pointer to the value of this enum as a trivial pointer with the known primitive type
                if let Some(underlying_type) = enum_type.underlying_type_no_target_no_constants() &&
                    let Some(underlying_inner_type) = Self::generate_primitive_type(&underlying_type) {
                    Ok(quote! {gospel_runtime::static_type_wrappers::TrivialPtr::<M, #underlying_inner_type>})
                } else {
                    // Otherwise, we have to generate it as a void ptr
                    Ok(quote! { gospel_runtime::static_type_wrappers::VoidPtr::<M> })
                }
            }
        }
    }
    fn is_opaque_type_index(&self, type_index: usize) -> bool {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        if let Type::Primitive(primitive_type) = type_definition {
            *primitive_type == PrimitiveType::Void
        } else { false }
    }
    fn generate_type_field_definition(&self, type_name: &Ident, source_file_name: &str, field_name: &Ident, maybe_field_type_index: Option<usize>, is_prototype_field: bool, function_closure: &Option<GospelVMClosure>) -> TokenStream {
        let field_doc_comment = Self::generate_doc_comment(function_closure, &format!("doc_{}", source_file_name));
        if let Some(field_type_index) = maybe_field_type_index && !self.is_opaque_type_index(field_type_index) &&
            let Ok(generated_field_type) = self.generate_type_reference(field_type_index) {
            if is_prototype_field {
                quote! { gsb_codegen_implement_field!(#type_name, #field_name, #source_file_name, optional, { #field_doc_comment }, #generated_field_type); }
            } else {
                quote! { gsb_codegen_implement_field!(#type_name, #field_name, #source_file_name, required, { #field_doc_comment }, #generated_field_type); }
            }
        } else {
            // We cannot generate an accurate field type, so just return DynamicPtr as-is
            if is_prototype_field {
                quote! { gsb_codegen_implement_field!(#type_name, #field_name, #source_file_name, optional, { #field_doc_comment }); }
            } else {
                quote! { gsb_codegen_implement_field!(#type_name, #field_name, #source_file_name, required, { #field_doc_comment }); }
            }
        }
    }
    fn generate_type_definition(&self, type_index: usize, is_parameterless_type: bool, function_closure: &Option<GospelVMClosure>) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_container = self.module_context.run_context.type_container_by_index(base_type_index);

        let user_defined_type = if let Type::UDT(wrapped_user_defined_type) = &type_container.wrapped_type {
            wrapped_user_defined_type
        } else { bail!("Type #{} is not a user defined type", base_type_index) };

        let full_type_name = user_defined_type.name.clone().ok_or_else(|| anyhow!("Cannot generate bindings for unnamed UDTs"))?;
        let type_name = Ident::new(&Self::generate_short_udt_name(&full_type_name), Span::call_site());
        let type_doc_comment = Self::generate_doc_comment(function_closure, "doc");
        let mut generated_field_names: HashSet<String> = HashSet::new();
        let mut generated_fields: Vec<TokenStream> = Vec::new();

        // Generate non-prototype members first
        for udt_member in &user_defined_type.members {
            if let UserDefinedTypeMember::Field(field) = udt_member && let Some(field_name) = field.name.as_ref() && !field_name.contains("@") {
                let field_tokens = self.generate_type_field_definition(&type_name, field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()), Some(field.member_type_index), false, function_closure);
                generated_field_names.insert(field_name.clone());
                generated_fields.push(field_tokens);
            }
        }

        // Sort prototype members by name to have consistent generated code layout
        let mut sorted_prototypes = type_container.member_prototypes.as_ref()
            .map(|x| x.iter().cloned().collect::<Vec<UserDefinedTypeMember>>())
            .unwrap_or(Vec::default());
        sorted_prototypes.sort_by(|a, b| a.name().cmp(&b.name()));

        // Prototype fields can have multiple definitions with conflicting types. We want to generate such fields only once and with opaque type
        let mut prototype_field_type_tracking: HashMap<String, usize> = HashMap::new();
        let mut prototype_fields_with_conflicting_types: HashSet<String> = HashSet::new();
        for prototype_udt_member in &sorted_prototypes {
            if let UserDefinedTypeMember::Field(field) = prototype_udt_member && let Some(field_name) = field.name.as_ref() && !generated_field_names.contains(field_name) {
                if let Some(existing_field_type_index) = prototype_field_type_tracking.get(field_name) {
                    if *existing_field_type_index != field.member_type_index {
                        prototype_fields_with_conflicting_types.insert(field_name.clone());
                    }
                } else {
                    prototype_field_type_tracking.insert(field_name.clone(), field.member_type_index);
                }
            }
        }

        // Generate optional prototype members now if non-prototype version has not been generated
        for prototype_udt_member in &sorted_prototypes {
            if let UserDefinedTypeMember::Field(field) = prototype_udt_member &&
                let Some(field_name) = field.name.as_ref() && !generated_field_names.contains(field_name) {
                let field_type = if prototype_fields_with_conflicting_types.contains(field_name) { None } else { Some(field.member_type_index) };
                let field_tokens = self.generate_type_field_definition(&type_name, field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()), field_type, true, function_closure);
                generated_field_names.insert(field_name.clone());
                generated_fields.push(field_tokens);
            }
        }
        let static_type_impl = if is_parameterless_type {
            Some(quote! { gsb_codegen_implement_static_type!(#type_name, #full_type_name); })
        } else { None };
        Ok(quote! {
            gsb_codegen_generate_type_struct!(#type_name, #full_type_name, { #type_doc_comment });
            #static_type_impl
            impl<M: gospel_runtime::memory_access::Memory> #type_name<M> {
                #(#generated_fields)*
            }
        })
    }
    fn generate_fallback_type_definition(&self, raw_type_name: &str) -> TokenStream {
        let type_name = Ident::new(&Self::generate_short_udt_name(&raw_type_name), Span::call_site());
        quote! { type #type_name<M: gospel_runtime::memory_access::Memory> = gospel_runtime::static_type_wrappers::VoidPtr<M>; }
    }
    pub(crate) fn generate_bindings_file(self) -> anyhow::Result<String> {
        let mut type_definitions: Vec<TokenStream> = Vec::new();
        for (type_name, maybe_type_index, is_parameterless_type, function_closure) in &self.module_context.type_name_to_type_index {
            if let Some(type_index) = maybe_type_index.clone() && let Ok(result_type_definition) = self.generate_type_definition(type_index, *is_parameterless_type, function_closure) {
                type_definitions.push(result_type_definition.clone());
            } else {
                let fallback_type_definition = self.generate_fallback_type_definition(type_name);
                type_definitions.push(fallback_type_definition);
            }
        }
        let bindings_mod_name = Ident::new(&self.bindings_mod_name, Span::call_site());
        let result_file_token_stream = quote! {
            #[macro_use(gsb_codegen_generate_type_struct, gsb_codegen_implement_field, gsb_codegen_implement_static_type)]
            extern crate gospel_runtime;

            #[allow(warnings, unused)]
            mod #bindings_mod_name {
                #(#type_definitions)*
            }
        };
        let parsed_file = parse2::<File>(result_file_token_stream.clone()).map_err(|x| anyhow!("Failed to parse generated file: {}\n{}", x, result_file_token_stream))?;
        Ok(prettyplease::unparse(&parsed_file))
    }
}
