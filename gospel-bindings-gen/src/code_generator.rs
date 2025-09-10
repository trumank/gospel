use std::cell::RefCell;
use crate::module_processor::{BindingsTypeDefinition, ResolvedBindingsModuleContext};
use anyhow::{anyhow, bail};
use gospel_typelib::type_model::{EnumType, PrimitiveType, Type, TypeGraphLike, UserDefinedType, UserDefinedTypeMember};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::collections::{HashMap, HashSet};
use convert_case::{Case, Casing};
use syn::{parse2, parse_str, File};
use gospel_compiler::ast::ExpressionValueType;
use gospel_vm::vm::{GospelVMTypeContainer, GospelVMValue};

#[derive(Debug)]
pub(crate) struct CodeGenerationContext {
    pub(crate) module_context: ResolvedBindingsModuleContext,
    pub(crate) bindings_mod_name: String,
    pub(crate) extra_definitions: RefCell<Vec<TokenStream>>,
    pub(crate) generated_extra_types: RefCell<HashSet<String>>,
}
impl CodeGenerationContext {
    fn generate_primitive_type(primitive_type: &PrimitiveType) -> TokenStream {
        match primitive_type {
            PrimitiveType::Void => quote!{ () },
            PrimitiveType::Char => quote!{ i8 },
            PrimitiveType::UnsignedChar => quote!{ u8 },
            PrimitiveType::WideChar => quote! { gospel_runtime::static_type_wrappers::WideChar },
            PrimitiveType::ShortInt => quote!{ i16 },
            PrimitiveType::UnsignedShortInt => quote!{ u16 },
            PrimitiveType::Int => quote!{ i32 },
            PrimitiveType::UnsignedInt => quote!{ u32 },
            PrimitiveType::Float => quote!{ f32 },
            PrimitiveType::Double => quote!{ f64 },
            PrimitiveType::Bool => quote!{ bool },
            PrimitiveType::LongInt => quote! { gospel_runtime::static_type_wrappers::LongInt },
            PrimitiveType::UnsignedLongInt => quote! { gospel_runtime::static_type_wrappers::UnsignedLongInt },
            PrimitiveType::LongLongInt => quote!{ i64 },
            PrimitiveType::UnsignedLongLongInt => quote!{ u64 },
            PrimitiveType::Char8 => quote!{ u8 },
            PrimitiveType::Char16 => quote!{ u16 },
            PrimitiveType::Char32 => quote!{ u32 },
        }
    }
    fn generate_short_type_name(type_name: &str) -> String {
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
        let short_type_name = Ident::new(&Self::generate_short_type_name(type_name), Span::call_site());
        let mod_name = Ident::new(&self.bindings_mod_name, Span::call_site());
        quote! { #crate_name::#mod_name::#short_type_name }
    }
    fn generate_doc_comment(type_definition: &BindingsTypeDefinition, doc_metadata: &str) -> Option<TokenStream> {
        let documentation_attributes: Vec<TokenStream> = type_definition.function_declaration.as_ref().unwrap().metadata.get(doc_metadata).into_iter()
            .flat_map(|x| x.lines())
            .filter(|x| !x.is_empty())
            .map(|doc_comment_line| quote! { #[doc = #doc_comment_line] })
            .collect();
        if documentation_attributes.is_empty() { None } else { Some(quote!{ #(#documentation_attributes)* }) }
    }
    fn generate_primitive_value_as_type(&self, primitive_value: u64) -> TokenStream {
        let type_name = format!("IntegralConst_0x{:X}", primitive_value);
        let type_ident = Ident::new(&type_name, Span::call_site());
        if !self.generated_extra_types.borrow().contains(&type_name) {
            let type_def = quote!{
                pub enum #type_ident {}
                impl gospel_runtime::static_type_wrappers::IntegralValueTypeTag for #type_ident { fn get_raw_integral_value() -> u64 { #primitive_value } }
            };
            self.extra_definitions.borrow_mut().push(type_def);
            self.generated_extra_types.borrow_mut().insert(type_name);
        }
        quote!{ #type_ident }
    }
    fn generate_vm_value_as_type(&self, value: &GospelVMValue) -> TokenStream {
        match value {
            GospelVMValue::TypeReference(type_index) => self.generate_type_reference(*type_index),
            GospelVMValue::Primitive(primitive_value) => self.generate_primitive_value_as_type(*primitive_value),
            _ => panic!("Unsupported type argument value type: {}", value)
        }
    }
    fn generate_type_reference(&self, type_index: usize) -> TokenStream {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);

        match type_definition {
            Type::Array(array_type) => {
                let pointee_type = self.generate_type_reference(array_type.element_type_index);
                quote! {gospel_runtime::static_type_wrappers::StaticArray::<#pointee_type>}
            },
            Type::Pointer(pointer_type) => {
                let pointee_type = self.generate_type_reference(pointer_type.pointee_type_index);
                if pointer_type.is_reference {
                    quote! {gospel_runtime::static_type_wrappers::Ref::<M, #pointee_type>}
                } else {
                    quote! {gospel_runtime::static_type_wrappers::Ptr::<M, #pointee_type>}
                }
            }
            Type::CVQualified(cv_qualified_type) => {
                self.generate_type_reference(cv_qualified_type.base_type_index)
            }
            Type::Primitive(primitive_type) => {
                Self::generate_primitive_type(primitive_type)
            }
            Type::Function(_) => {
                // Generate functions as void types due to the fact that their precise type is not useful in the context of external process bindings
                quote! { () }
            }
            Type::UDT(user_defined_type) => {
                let type_container = self.module_context.run_context.type_container_by_index(base_type_index);
                if let Some(udt_name) = &user_defined_type.name && let Some(source_crate_name) = self.module_context.type_source_crate_lookup.get(udt_name) {
                    // Try to generate as an explicit UDT definition within source crate
                    let full_type_name = self.generate_type_qualified_name(source_crate_name, udt_name);

                    if let Some(function_arguments) = &type_container.source_function_args && !function_arguments.is_empty() {
                        let type_arguments: Vec<TokenStream> = function_arguments.iter().map(|x| self.generate_vm_value_as_type(x)).collect();
                        quote! { #full_type_name<#(#type_arguments),*> }
                    } else {
                        quote! { #full_type_name }
                    }
                } else {
                    quote! { () }
                }
            }
            Type::Enum(enum_type) => {
                // TODO: We could generate more accurate bindings based not just on the name of the type but also on the template parameters
                if let Some(enum_name) = &enum_type.name && let Some(source_crate_name) = self.module_context.type_source_crate_lookup.get(enum_name) {
                    // Try to generate as an explicit enum definition within source crate first
                    let full_type_name = self.generate_type_qualified_name(source_crate_name, enum_name);
                    quote! { #full_type_name }
                } else if let Some(underlying_primitive_type) = enum_type.underlying_type_no_target_no_constants() {
                    // Fall back to the explicitly specified underlying type if it can be determined without looking up target platform or constants
                    let underlying_type = Self::generate_primitive_type(&underlying_primitive_type);
                    quote! {gospel_runtime::static_type_wrappers::TrivialPtr::<M, #underlying_type>}
                } else {
                    // If there is no code generated stub for this enum, and its type is also not known, return unit type
                    quote! { () }
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
    fn generate_type_field_definition(&self, source_file_name: &str, field_name: &Ident, maybe_field_type_index: Option<usize>, is_prototype_field: bool, type_definition: &BindingsTypeDefinition) -> TokenStream {
        let field_doc_comment = Self::generate_doc_comment(type_definition, &format!("doc_{}", source_file_name));
        if let Some(field_type_index) = maybe_field_type_index && !self.is_opaque_type_index(field_type_index) {
            let field_type = self.generate_type_reference(field_type_index);
            if is_prototype_field {
                quote! { gsb_codegen_implement_udt_field!(#field_name, #source_file_name, optional, { #field_doc_comment }, #field_type); }
            } else {
                quote! { gsb_codegen_implement_udt_field!(#field_name, #source_file_name, required, { #field_doc_comment }, #field_type); }
            }
        } else {
            // We cannot generate an accurate field type, so just return DynamicPtr as-is
            if is_prototype_field {
                quote! { gsb_codegen_implement_udt_field!(#field_name, #source_file_name, optional, { #field_doc_comment }); }
            } else {
                quote! { gsb_codegen_implement_udt_field!(#field_name, #source_file_name, required, { #field_doc_comment }); }
            }
        }
    }
    fn generate_parameter_declaration(parameter_name: &Ident, parameter_type: &ExpressionValueType) -> (TokenStream, TokenStream) {
        match parameter_type {
            // TODO: This should be BoolValueTypeTag but due to current implementation of VM value conversion for type references it cannot be
            ExpressionValueType::Bool => (quote! {
                #parameter_name : gospel_runtime::static_type_wrappers::IntegralValueTypeTag
            }, quote! {
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Integer(_) => (quote! {
                #parameter_name : gospel_runtime::static_type_wrappers::IntegralValueTypeTag
            }, quote!{
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Typename => (quote!{
                #parameter_name : gospel_runtime::static_type_wrappers::StaticTypeTag + ?Sized
            }, quote!{
                gospel_typelib::type_model::TypeTemplateArgument::Type(#parameter_name::store_type_descriptor(namespace))
            }),
            _ => panic!("Unhandled type parameter expression type: {}", parameter_type)
        }
    }
    fn generate_udt_definition(&self, user_defined_type: &UserDefinedType, type_container: &GospelVMTypeContainer, type_definition: &BindingsTypeDefinition) -> TokenStream {
        let full_type_name = user_defined_type.name.clone().unwrap();
        let type_doc_comment = Self::generate_doc_comment(type_definition, "doc");
        let mut generated_field_names: HashSet<String> = HashSet::new();
        let mut generated_fields: Vec<TokenStream> = Vec::new();

        // Generate non-prototype members first
        for udt_member in &user_defined_type.members {
            if let UserDefinedTypeMember::Field(field) = udt_member && let Some(field_name) = field.name.as_ref() && !field_name.contains("@") {
                let field_tokens = self.generate_type_field_definition(field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()),
                    Some(field.member_type_index), false, type_definition);
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
                let field_tokens = self.generate_type_field_definition(field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()), field_type, true, type_definition);
                generated_field_names.insert(field_name.clone());
                generated_fields.push(field_tokens);
            }
        }

        let type_name = Ident::new(&Self::generate_short_type_name(&full_type_name), Span::call_site());
        let function_signature = type_definition.function_declaration.as_ref().unwrap().reference.signature.clone();

        let mut parameter_declarations: Vec<TokenStream> = Vec::new();
        let mut parameter_list: Vec<Ident> = Vec::new();
        let mut parameter_call_arguments: Vec<TokenStream> = Vec::new();

        for implicit_parameter in function_signature.implicit_parameters {
            let parameter_name = Ident::new(implicit_parameter.parameter_declaration.upgrade().unwrap().name.as_str(), Span::call_site());
            let (parameter_declaration, parameter_call_argument) = Self::generate_parameter_declaration(&parameter_name, &implicit_parameter.parameter_type);
            parameter_declarations.push(parameter_declaration);
            parameter_list.push(parameter_name);
            parameter_call_arguments.push(parameter_call_argument);
        }
        if let Some(explicit_parameters) = function_signature.explicit_parameters.as_ref() {
            for explicit_parameter in explicit_parameters {
                let parameter_name = Ident::new(explicit_parameter.parameter_declaration.upgrade().unwrap().name.as_str(), Span::call_site());
                let (parameter_declaration, parameter_call_argument) = Self::generate_parameter_declaration(&parameter_name, &explicit_parameter.parameter_type);
                parameter_declarations.push(parameter_declaration);
                parameter_list.push(parameter_name);
                parameter_call_arguments.push(parameter_call_argument);
            }
        }

        let (merged_param_decl, merged_param_list, merged_call_args, merged_phantom_data, opaque_type_decl) = if !parameter_list.is_empty() {
            let opaque_type_name = Ident::new(&format!("Opaque{}", type_name.to_string()), Span::call_site());
            let phantom_data_list: Vec<TokenStream> = parameter_list.iter().map(|parameter_name| {
                let field_ident = Ident::new(&format!("_phantom_{}", parameter_name.to_string()), Span::call_site());
                quote!{ #field_ident: std::marker::PhantomData::<#parameter_name> }
            }).collect();
            let dynamic_type_tokens = quote! {
                #type_doc_comment
                #[doc = "Opaque types represent template instantiations without statically known arguments"]
                pub struct #opaque_type_name {
                    _dynamic_size_marker: [u8],
                }
                impl gospel_runtime::static_type_wrappers::DynamicTypeTag for #opaque_type_name {
                    fn get_cast_target_type_descriptor(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> Option<usize> {
                        if let Some(struct_type_name) = ptr_metadata.struct_type_name() && struct_type_name == #full_type_name {
                            Some(ptr_metadata.type_index)
                        } else if let Some(base_class_indices) = ptr_metadata.struct_find_all_base_classes_by_type_name(#full_type_name) && base_class_indices.len() == 1 {
                            Some(base_class_indices[0])
                        } else { None }
                    }
                }
                impl #opaque_type_name {
                    #(#generated_fields)*
                }
            };
            (Some(quote!{ <#(#parameter_declarations),*> }), Some(quote!{ <#(#parameter_list),*> }), quote!{ vec![#(#parameter_call_arguments),*] }, Some(quote! { #(#phantom_data_list),*, }), Some(dynamic_type_tokens))
        } else { (None, None, quote!{ vec![] }, None, None) };
        quote! {
            #type_doc_comment
            pub struct #type_name #merged_param_decl {
                #merged_phantom_data
                _dynamic_size_marker: [u8],
            }
            impl #merged_param_decl gospel_runtime::static_type_wrappers::StaticTypeTag for #type_name #merged_param_list {
                fn store_type_descriptor(namespace: &gospel_runtime::runtime_type_model::TypePtrNamespace) -> usize {
                    use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
                    use crate::gospel_runtime::static_type_wrappers::IntegralValueTypeTag;
                    let type_arguments: Vec<gospel_typelib::type_model::TypeTemplateArgument> = #merged_call_args;
                    let mut type_graph = namespace.type_graph.write().unwrap();
                    type_graph.create_named_type(#full_type_name, type_arguments).unwrap().unwrap_or_else(|| panic!("Named UDT type not found: {}", #full_type_name))
                }
            }
            impl #merged_param_decl gospel_runtime::static_type_wrappers::DynamicTypeTag for #type_name #merged_param_list {
                fn get_cast_target_type_descriptor(ptr_metadata: &gospel_runtime::runtime_type_model::TypePtrMetadata) -> Option<usize> {
                    use crate::gospel_runtime::static_type_wrappers::StaticTypeTag;
                    Some(Self::store_type_descriptor(&ptr_metadata.namespace))
                }
            }
            impl #merged_param_decl #type_name #merged_param_list {
                #(#generated_fields)*
            }
            #opaque_type_decl
        }
    }
    fn generate_enum_constant_definition(&self, enum_definition: &BindingsTypeDefinition, type_name: &Ident, enum_underlying_type: &Option<PrimitiveType>, source_constant_name: &str, constant_name: Ident, is_prototype_constant: bool) -> TokenStream {
        let field_doc_comment = Self::generate_doc_comment(enum_definition, &format!("doc_{}", source_constant_name));
        let type_impl_kind = if enum_definition.is_parameterless_type() { quote! { static_type } } else { quote!{ dynamic_type } };
        if let Some(explicit_underlying_type) = enum_underlying_type {
            let underlying_type = Self::generate_primitive_type(explicit_underlying_type);
            if is_prototype_constant {
                quote! { gsb_codegen_implement_enum_constant!(#type_name, #constant_name, #source_constant_name, #type_impl_kind, optional, { #field_doc_comment }, #underlying_type); }
            } else {
                quote! { gsb_codegen_implement_enum_constant!(#type_name, #constant_name, #source_constant_name, #type_impl_kind, required, { #field_doc_comment }, #underlying_type); }
            }
        } else {
            if is_prototype_constant {
                quote! { gsb_codegen_implement_enum_constant!(#type_name, #constant_name, #source_constant_name, #type_impl_kind, optional, { #field_doc_comment }); }
            } else {
                quote! { gsb_codegen_implement_enum_constant!(#type_name, #constant_name, #source_constant_name, #type_impl_kind, required, { #field_doc_comment }); }
            }
        }
    }
    fn generate_enum_definition(&self, enum_type: &EnumType, type_container: &GospelVMTypeContainer, type_definition: &BindingsTypeDefinition) -> TokenStream {
        let full_type_name = enum_type.name.clone().unwrap();
        let type_name = Ident::new(&Self::generate_short_type_name(&full_type_name), Span::call_site());
        let type_doc_comment = Self::generate_doc_comment(type_definition, "doc");

        // Take u64 as the underlying type if we do not have an explicit underlying type specified, or we failed to evaluate it
        // In that case we have to read enum value as variable length integral value
        // TODO: This could be relaxed to also allow implicit underlying type for scoped enums (enum class) since it has platform-independent underlying type
        let enum_underlying_type: Option<PrimitiveType> = enum_type.underlying_type.clone();
        let type_impl_kind = if type_definition.is_parameterless_type() { quote! { static_type } } else { quote!{ dynamic_type } };
        let enum_inner_type = if enum_underlying_type.is_some() { Self::generate_primitive_type(enum_underlying_type.as_ref().unwrap()) } else { quote!{ u64 } };

        let mut generated_constant_names: HashSet<String> = HashSet::new();
        let mut generated_constants: Vec<TokenStream> = Vec::new();

        // Generate non-prototype constants first
        for constant_definition in &enum_type.constants {
            if let Some(constant_name) = constant_definition.name.as_ref() && !constant_name.contains("@") {
                generated_constant_names.insert(constant_name.clone());
                let constant_generated_name = Ident::new(&Self::convert_field_name_to_snake_case(constant_name), Span::call_site());
                generated_constants.push(self.generate_enum_constant_definition(type_definition, &type_name, &enum_underlying_type, constant_name.as_ref(), constant_generated_name, false));
            }
        }

        // Sort prototype constants by name to have consistent generated code layout
        let mut sorted_prototypes: Vec<String> = type_container.enum_constant_prototypes.as_ref().unwrap().iter().cloned().collect();
        sorted_prototypes.sort_by(|name_a, name_b| name_a.cmp(name_b));

        // Generate optional prototype constants if we have not previously generated them as non-prototype constants
        for prototype_constant_name in &sorted_prototypes {
            if !prototype_constant_name.contains("@") && !generated_constant_names.contains(prototype_constant_name) {
                generated_constant_names.insert(prototype_constant_name.clone());
                let constant_generated_name = Ident::new(&Self::convert_field_name_to_snake_case(prototype_constant_name), Span::call_site());
                generated_constants.push(self.generate_enum_constant_definition(type_definition, &type_name, &enum_underlying_type, prototype_constant_name.as_ref(), constant_generated_name, true));
            }
        }
        let trivial_value_impl_call = if enum_underlying_type.is_some() {
            quote! { gsb_codegen_implement_enum_trivial_value!(#type_name, #enum_inner_type); }
        } else { quote! { gsb_codegen_implement_enum_trivial_value!(#type_name); } };
        quote! {
            #type_doc_comment
            #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #[repr(transparent)]
            pub struct #type_name(pub #enum_inner_type);
            gsb_codegen_implement_enum_type!(#type_name, #full_type_name, #type_impl_kind);
            #trivial_value_impl_call
            impl #type_name {
                #(#generated_constants)*
            }
        }
    }
    fn generate_fallback_type_definition(&self, raw_type_name: &str) -> TokenStream {
        let type_name = Ident::new(&Self::generate_short_type_name(&raw_type_name), Span::call_site());
        quote! { type #type_name<M: gospel_runtime::memory_access::Memory> = (); }
    }
    pub(crate) fn generate_bindings_file(self) -> anyhow::Result<String> {
        let mut type_definitions: Vec<TokenStream> = Vec::new();
        for type_definition in &self.module_context.types_to_generate {
            if let Some(type_index) = type_definition.type_index {
                let base_type_index = self.module_context.run_context.base_type_index(type_index);
                let type_container = self.module_context.run_context.type_container_by_index(base_type_index);

                if let Type::UDT(user_defined_type) = &type_container.wrapped_type {
                    // Generate user defined type definition
                    let result_type_definition = self.generate_udt_definition(user_defined_type, type_container, type_definition);
                    type_definitions.push(result_type_definition.clone());
                } else if let Type::Enum(enum_type) = &type_container.wrapped_type {
                    let result_type_definition = self.generate_enum_definition(enum_type, type_container, type_definition);
                    type_definitions.push(result_type_definition);
                } else {
                    bail!("Expected UDT or enum type in types to generate list, found type definition not marked as either");
                }
            } else {
                // Generate fallback type definition if we failed to eval this type function (which should generally never happen for well-formed UDTs with partial types compiler switch)
                let fallback_type_definition = self.generate_fallback_type_definition(&type_definition.type_full_name);
                type_definitions.push(fallback_type_definition);
            }
        }
        let bindings_mod_name = Ident::new(&self.bindings_mod_name, Span::call_site());
        let bindings_extra_definitions = self.extra_definitions.borrow().clone();
        let result_file_token_stream = quote! {
            #[macro_use(gsb_codegen_implement_udt_field, gsb_codegen_implement_enum_type, gsb_codegen_implement_enum_trivial_value, gsb_codegen_implement_enum_constant)]
            #[allow(unused)]
            extern crate gospel_runtime;

            #[allow(warnings, unused)]
            mod #bindings_mod_name {
                #(#bindings_extra_definitions)*
                #(#type_definitions)*
            }
        };
        let parsed_file = parse2::<File>(result_file_token_stream.clone()).map_err(|x| anyhow!("Failed to parse generated file: {}\n{}", x, result_file_token_stream))?;
        Ok(prettyplease::unparse(&parsed_file))
    }
}
