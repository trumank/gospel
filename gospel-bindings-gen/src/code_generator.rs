use std::cell::RefCell;
use crate::module_processor::{BindingsTypeDefinition, ResolvedBindingsModuleContext};
use anyhow::{anyhow, bail};
use gospel_typelib::type_model::{EnumType, PrimitiveType, Type, TypeGraphLike, UserDefinedType, UserDefinedTypeMember};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::collections::{HashMap, HashSet};
use std::env::temp_dir;
use std::fs::write;
use std::path::{absolute, PathBuf};
use convert_case::{Case, Casing};
use syn::{parse2, parse_str, File};
use gospel_compiler::ast::ExpressionValueType;
use gospel_compiler::backend::CompilerFunctionSignature;
use gospel_vm::vm::{GospelVMTypeContainer, GospelVMValue};
use uuid::Uuid;
use crate::ModuleBindingsType;

#[derive(Debug)]
pub(crate) struct CodeGenerationContext {
    pub(crate) module_context: ResolvedBindingsModuleContext,
    pub(crate) bindings_type: ModuleBindingsType,
    pub(crate) type_universe_full_name: String,
    pub(crate) bindings_mod_name: String,
    pub(crate) extra_definitions: RefCell<Vec<TokenStream>>,
    pub(crate) generated_extra_types: RefCell<HashSet<String>>,
}

struct TypeParameterTokens {
    parameter_declaration: Option<TokenStream>,
    parameter_list: Option<TokenStream>,
    phantom_data_list: Option<TokenStream>,
    static_type_implementation: TokenStream,
}

impl CodeGenerationContext {
    fn generate_primitive_type(&self, primitive_type: &PrimitiveType) -> TokenStream {
        match primitive_type {
            PrimitiveType::Void => quote!{ () },
            PrimitiveType::Char => quote!{ i8 },
            PrimitiveType::UnsignedChar => quote!{ u8 },
            PrimitiveType::WideChar => match self.bindings_type {
                ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::PlatformWideChar },
                ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::ExternalWideChar },
            },
            PrimitiveType::ShortInt => quote!{ i16 },
            PrimitiveType::UnsignedShortInt => quote!{ u16 },
            PrimitiveType::Int => quote!{ i32 },
            PrimitiveType::UnsignedInt => quote!{ u32 },
            PrimitiveType::Float => quote!{ f32 },
            PrimitiveType::Double => quote!{ f64 },
            PrimitiveType::Bool => quote!{ bool },
            PrimitiveType::LongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::PlatformLongInt },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalLongInt },
            },
            PrimitiveType::UnsignedLongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::PlatformUnsignedLongInt },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalUnsignedLongInt },
            },
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
                impl gospel_runtime::core_type_definitions::IntegralValueTypeTag for #type_ident { fn get_raw_integral_value() -> u64 { #primitive_value } }
            };
            self.extra_definitions.borrow_mut().push(type_def);
            self.generated_extra_types.borrow_mut().insert(type_name);
        }
        quote!{ #type_ident }
    }
    fn generate_vm_value_as_type(&self, value: &GospelVMValue) -> anyhow::Result<TokenStream> {
        match value {
            GospelVMValue::TypeReference(type_index) => Ok(self.generate_type_reference(*type_index)?),
            GospelVMValue::Primitive(primitive_value) => Ok(self.generate_primitive_value_as_type(*primitive_value)),
            _ => bail!("Unsupported type argument value type: {}", value)
        }
    }
    fn generate_type_reference(&self, type_index: usize) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);

        Ok(match type_definition {
            Type::Array(array_type) => {
                let element_type = self.generate_type_reference(array_type.element_type_index)?;
                let array_length = self.generate_primitive_value_as_type(array_type.array_length as u64);
                match self.bindings_type {
                    ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::StaticArray::<#element_type, #array_length>},
                    ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::StaticArray::<#element_type, #array_length>},
                }
            },
            Type::Pointer(pointer_type) => {
                let pointee_type = self.generate_type_reference(pointer_type.pointee_type_index)?;
                if pointer_type.is_reference {
                    match self.bindings_type {
                        ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::CRef::<#pointee_type>},
                        ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::Ref::<M, #pointee_type>},
                    }
                } else {
                    match self.bindings_type {
                        ModuleBindingsType::Local => quote! {Option<gospel_runtime::local_type_model::CRef::<#pointee_type>>},
                        ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::Ptr::<M, #pointee_type>},
                    }
                }
            }
            Type::CVQualified(cv_qualified_type) => {
                self.generate_type_reference(cv_qualified_type.base_type_index)?
            }
            Type::Primitive(primitive_type) => {
                self.generate_primitive_type(primitive_type)
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
                        let type_arguments: Vec<TokenStream> = function_arguments.iter().map(|x| self.generate_vm_value_as_type(x)).collect::<anyhow::Result<Vec<TokenStream>>>()?;
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
                    self.generate_primitive_type(&underlying_primitive_type)
                } else {
                    // If there is no code generated stub for this enum, and its type is also not known, return unit type
                    quote! { () }
                }
            }
        })
    }
    fn is_opaque_type_index(&self, type_index: usize) -> bool {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        if let Type::Primitive(primitive_type) = type_definition {
            *primitive_type == PrimitiveType::Void
        } else { false }
    }
    fn generate_type_field_definition(&self, source_file_name: &str, field_name: &Ident, maybe_field_type_index: Option<usize>, is_prototype_field: bool, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let field_doc_comment = Self::generate_doc_comment(type_definition, &format!("doc_{}", source_file_name));
        Ok(if let Some(field_type_index) = maybe_field_type_index && !self.is_opaque_type_index(field_type_index) {
            let field_type = self.generate_type_reference(field_type_index)?;
            match self.bindings_type {
                ModuleBindingsType::External => {
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, optional, { #field_doc_comment }, #field_type); }
                    } else {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, required, { #field_doc_comment }, #field_type); }
                    }
                }
                ModuleBindingsType::Local => {
                    let type_universe = Ident::new(&self.type_universe_full_name, Span::call_site());
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, optional, { #field_doc_comment }, #field_type); }
                    } else {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, required, { #field_doc_comment }, #field_type); }
                    }
                }
            }
        } else {
            // We cannot generate an accurate field type, so just return DynamicPtr as-is
            match self.bindings_type {
                ModuleBindingsType::External => {
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, optional, { #field_doc_comment }); }
                    } else {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, required, { #field_doc_comment }); }
                    }
                }
                ModuleBindingsType::Local => {
                    let type_universe = Ident::new(&self.type_universe_full_name, Span::call_site());
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, optional, { #field_doc_comment }); }
                    } else {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, required, { #field_doc_comment }); }
                    }
                }
            }
        })
    }
    fn generate_parameter_declaration(parameter_name: &Ident, parameter_type: &ExpressionValueType) -> anyhow::Result<(TokenStream, TokenStream)> {
        Ok(match parameter_type {
            // TODO: This should be BoolValueTypeTag but due to current implementation of VM value conversion for type references it cannot be
            ExpressionValueType::Bool => (quote! {
                #parameter_name : gospel_runtime::core_type_definitions::IntegralValueTypeTag
            }, quote! {
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Integer(_) => (quote! {
                #parameter_name : gospel_runtime::core_type_definitions::IntegralValueTypeTag
            }, quote!{
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Typename => (quote!{
                #parameter_name : gospel_runtime::core_type_definitions::StaticTypeTag + ?Sized
            }, quote!{
                gospel_typelib::type_model::TypeTemplateArgument::Type(#parameter_name::store_type_descriptor_raw(type_graph, target_triplet, type_cache))
            }),
            _ => { bail!("Unhandled type parameter expression type: {}", parameter_type); }
        })
    }
    fn generate_type_parameters_from_function_signature(&self, type_name: &Ident, full_type_name: &str, function_signature: &CompilerFunctionSignature) -> anyhow::Result<TypeParameterTokens> {
        let mut parameter_declarations: Vec<TokenStream> = Vec::new();
        let mut parameter_list: Vec<Ident> = Vec::new();
        let mut parameter_call_arguments: Vec<TokenStream> = Vec::new();

        for implicit_parameter in &function_signature.implicit_parameters {
            let parameter_name = Ident::new(implicit_parameter.parameter_declaration.upgrade().unwrap().name.as_str(), Span::call_site());
            let (parameter_declaration, parameter_call_argument) = Self::generate_parameter_declaration(&parameter_name, &implicit_parameter.parameter_type)?;
            parameter_declarations.push(parameter_declaration);
            parameter_list.push(parameter_name);
            parameter_call_arguments.push(parameter_call_argument);
        }
        if let Some(explicit_parameters) = function_signature.explicit_parameters.as_ref() {
            for explicit_parameter in explicit_parameters {
                let parameter_name = Ident::new(explicit_parameter.parameter_declaration.upgrade().unwrap().name.as_str(), Span::call_site());
                let (parameter_declaration, parameter_call_argument) = Self::generate_parameter_declaration(&parameter_name, &explicit_parameter.parameter_type)?;
                parameter_declarations.push(parameter_declaration);
                parameter_list.push(parameter_name);
                parameter_call_arguments.push(parameter_call_argument);
            }
        }

        let mut merged_parameter_declaration: Option<TokenStream> = None;
        let mut merged_parameter_list: Option<TokenStream> = None;
        let mut merged_phantom_data_list: Option<TokenStream> = None;
        let static_type_implementation: TokenStream;

        if !parameter_list.is_empty() {
            merged_parameter_declaration = Some(quote!{ <#(#parameter_declarations),*> });
            merged_parameter_list = Some(quote!{ <#(#parameter_list),*> });

            let phantom_data_list: Vec<TokenStream> = parameter_list.iter().map(|parameter_name| {
                let field_ident = Ident::new(&format!("_phantom_{}", parameter_name.to_string()), Span::call_site());
                quote!{ #field_ident: std::marker::PhantomData::<#parameter_name> }
            }).collect();
            merged_phantom_data_list = Some(quote! { #(#phantom_data_list),*, });

            static_type_implementation = quote! {
                impl #merged_parameter_declaration gospel_runtime::core_type_definitions::StaticTypeTag for #type_name #merged_parameter_list {
                    fn store_type_descriptor_raw(type_graph: &std::sync::RwLock<dyn gospel_typelib::type_model::MutableTypeGraph>, target_triplet: gospel_typelib::target_triplet::TargetTriplet, type_cache: &std::sync::Mutex<gospel_runtime::core_type_definitions::StaticTypeLayoutCache>) -> usize {
                        use gospel_runtime::core_type_definitions::StaticTypeTag;
                        use gospel_runtime::core_type_definitions::IntegralValueTypeTag;
                        let type_arguments: Vec<gospel_typelib::type_model::TypeTemplateArgument> = vec![#(#parameter_call_arguments),*];
                        let mut writeable_type_graph = type_graph.write().unwrap();
                        writeable_type_graph.create_named_type(#full_type_name, type_arguments).unwrap().unwrap_or_else(|| panic!("Named UDT type not found: {}", #full_type_name))
                    }
                }
            };
        } else {
            // No type parameters for this type, we can use a faster cached version keyed by type name
            static_type_implementation = quote! {
                impl gospel_runtime::core_type_definitions::StaticTypeTag for #type_name {
                    fn store_type_descriptor_raw(type_graph: &std::sync::RwLock<dyn gospel_typelib::type_model::MutableTypeGraph>, target_triplet: gospel_typelib::target_triplet::TargetTriplet, type_cache: &std::sync::Mutex<gospel_runtime::core_type_definitions::StaticTypeLayoutCache>) -> usize {
                        type_cache.lock().unwrap().get_static_type_index_cached(type_graph, #full_type_name).unwrap_or_else(|| panic!("Named UDT type not found: {}", #full_type_name))
                    }
                }
            };
        }
        Ok(TypeParameterTokens{
            parameter_declaration: merged_parameter_declaration,
            parameter_list: merged_parameter_list,
            phantom_data_list: merged_phantom_data_list,
            static_type_implementation,
        })
    }
    fn generate_udt_definition(&self, user_defined_type: &UserDefinedType, type_container: &GospelVMTypeContainer, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let full_type_name = user_defined_type.name.clone().unwrap();
        let type_doc_comment = Self::generate_doc_comment(type_definition, "doc");
        let mut generated_field_names: HashSet<String> = HashSet::new();
        let mut generated_fields: Vec<TokenStream> = Vec::new();

        // Generate non-prototype members first
        for udt_member in &user_defined_type.members {
            if let UserDefinedTypeMember::Field(field) = udt_member && let Some(field_name) = field.name.as_ref() && !field_name.contains("@") {
                let field_tokens = self.generate_type_field_definition(field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()),
                    Some(field.member_type_index), false, type_definition)?;
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
                let field_tokens = self.generate_type_field_definition(field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()), field_type, true, type_definition)?;
                generated_field_names.insert(field_name.clone());
                generated_fields.push(field_tokens);
            }
        }

        let type_name = Ident::new(&Self::generate_short_type_name(&full_type_name), Span::call_site());
        let function_signature = type_definition.function_declaration.as_ref().unwrap().reference.signature.clone();
        let TypeParameterTokens{ parameter_declaration, parameter_list, phantom_data_list, static_type_implementation } =
            self.generate_type_parameters_from_function_signature(&type_name, &full_type_name, &function_signature)?;

        let mut all_type_implementations: Vec<TokenStream> = Vec::new();
        all_type_implementations.push(static_type_implementation);

        if self.bindings_type == ModuleBindingsType::Local {
            let type_universe = Ident::new(&self.type_universe_full_name, Span::call_site());
            all_type_implementations.push(quote! {
                impl #parameter_declaration gospel_runtime::local_type_model::ImplicitPtrMetadata for #type_name #parameter_list {
                    fn create_implicit_metadata() -> Self::Metadata {
                        use generic_statics::{define_namespace, Namespace};
                        define_namespace!(TypeDescriptor);
                        let (type_size, _) = TypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().get_type_size_and_alignment();
                        type_size
                    }
                    fn static_align_of_val() -> usize {
                        use generic_statics::{define_namespace, Namespace};
                        define_namespace!(TypeDescriptor);
                        let (_, type_alignment) = TypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().get_type_size_and_alignment();
                        type_alignment
                    }
                }
            });
            if type_definition.function_declaration.as_ref().unwrap().metadata.contains_key("attr_bitwise_copyable") {
                all_type_implementations.push(quote! {
                    unsafe impl #parameter_declaration std::clone::CloneToUninit for #type_name #parameter_list {
                        unsafe fn clone_to_uninit(&self, dest: *mut u8) {
                            dest.copy_from(self._private_bytes.as_ptr(), Self::static_size_of_val());
                        }
                    }
                });
            }
            if type_definition.function_declaration.as_ref().unwrap().metadata.contains_key("attr_zero_constructible") {
                all_type_implementations.push(quote! {
                    unsafe impl #parameter_declaration gospel_runtime::local_type_model::DefaultConstructAtUninit for #type_name #parameter_list {
                        unsafe fn default_construct_at(dest: *mut u8) {
                            dest.write_bytes(0, Self::static_size_of_val());
                        }
                    }
                });
            }
        }

        let type_inner_field: TokenStream = match self.bindings_type {
            ModuleBindingsType::Local => quote! { _private_bytes: [u8] },
            ModuleBindingsType::External => quote! { _private_constructor_marker: u8 },
        };

        Ok(quote! {
            #type_doc_comment
            pub struct #type_name #parameter_declaration {
                #phantom_data_list
                #type_inner_field
            }
            #(#all_type_implementations)*
            impl #parameter_declaration #type_name #parameter_list {
                #(#generated_fields)*
            }
        })
    }
    fn generate_enum_constant_definition(&self, enum_definition: &BindingsTypeDefinition, enum_underlying_type: &Option<PrimitiveType>, source_constant_name: &str, constant_name: Ident, is_prototype_constant: bool) -> TokenStream {
        let field_doc_comment = Self::generate_doc_comment(enum_definition, &format!("doc_{}", source_constant_name));
        match self.bindings_type {
            ModuleBindingsType::External => {
                if is_prototype_constant {
                    quote! { gsb_codegen_implement_external_enum_constant!(#constant_name, #source_constant_name, optional, { #field_doc_comment }); }
                } else {
                    quote! { gsb_codegen_implement_external_enum_constant!(#constant_name, #source_constant_name, required, { #field_doc_comment }); }
                }
            }
            ModuleBindingsType::Local => {
                let type_universe = Ident::new(&self.type_universe_full_name, Span::call_site());
                if enum_underlying_type.is_some() {
                    if is_prototype_constant {
                        quote! { gsb_codegen_implement_local_enum_constant!(#constant_name, #source_constant_name, #type_universe, sized, optional, { #field_doc_comment }); }
                    } else {
                        quote! { gsb_codegen_implement_local_enum_constant!(#constant_name, #source_constant_name, #type_universe, sized, required, { #field_doc_comment }); }
                    }
                } else {
                    if is_prototype_constant {
                        quote! { gsb_codegen_implement_local_enum_constant!(#constant_name, #source_constant_name, #type_universe, boxed, optional, { #field_doc_comment }); }
                    } else {
                        quote! { gsb_codegen_implement_local_enum_constant!(#constant_name, #source_constant_name, #type_universe, boxed, required, { #field_doc_comment }); }
                    }
                }
            }
        }
    }
    /// Calculates underlying type of the enum at the given type index by checking its flags and target triplet
    fn calculate_enum_underlying_type(&self, type_index: usize) -> anyhow::Result<Option<PrimitiveType>> {
        let type_container = self.module_context.run_context.type_container_by_index(type_index);
        let enum_type = if let Type::Enum(enum_type) = &type_container.wrapped_type { enum_type } else { bail!("Type at index not an enum") };

        // Calculate the underlying type of the enum based on the type container given
        if !type_container.enum_underlying_type_unknown {
            if let Some(target_triplet) = self.module_context.run_context.target_triplet() {
                // We have a target triplet, if the type is not partial, use underlying_type, otherwise use underlying_type_no_constants
                if type_container.partial_type {
                    Ok(enum_type.underlying_type_no_constants(target_triplet))
                } else { Ok(Some(enum_type.underlying_type(target_triplet)?)) }
            } else {
                // We have no target triplet, so attempt to calculate the underlying type from scoped-ness and explicit type given
                Ok(enum_type.underlying_type_no_target_no_constants())
            }
        } else {
            // Underlying type is explicitly marked as unknown, so we cannot do anything at this point
            Ok(None)
        }
    }

    fn generate_enum_definition(&self, enum_type: &EnumType, type_container: &GospelVMTypeContainer, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let full_type_name = enum_type.name.clone().unwrap();
        let type_name = Ident::new(&Self::generate_short_type_name(&full_type_name), Span::call_site());
        let type_doc_comment = Self::generate_doc_comment(type_definition, "doc");

        let underlying_type = self.calculate_enum_underlying_type(type_definition.type_index.unwrap())?;
        let mut generated_constant_names: HashSet<String> = HashSet::new();
        let mut generated_constants: Vec<TokenStream> = Vec::new();

        // Generate non-prototype constants first
        for constant_definition in &enum_type.constants {
            if let Some(constant_name) = constant_definition.name.as_ref() && !constant_name.contains("@") {
                generated_constant_names.insert(constant_name.clone());
                let constant_generated_name = Ident::new(&Self::convert_field_name_to_snake_case(constant_name), Span::call_site());
                generated_constants.push(self.generate_enum_constant_definition(type_definition, &underlying_type, constant_name.as_ref(), constant_generated_name, false));
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
                generated_constants.push(self.generate_enum_constant_definition(type_definition, &underlying_type, prototype_constant_name.as_ref(), constant_generated_name, true));
            }
        }

        let function_signature = type_definition.function_declaration.as_ref().unwrap().reference.signature.clone();
        let TypeParameterTokens{ parameter_declaration, parameter_list, phantom_data_list, static_type_implementation } =
            self.generate_type_parameters_from_function_signature(&type_name, &full_type_name, &function_signature)?;

        let mut all_type_implementations: Vec<TokenStream> = Vec::new();
        all_type_implementations.push(static_type_implementation);

        let type_inner_field: TokenStream;
        let mut type_additional_attributes: Option<TokenStream> = None;

        if self.bindings_type == ModuleBindingsType::External {
            if let Some(known_underlying_type) = underlying_type {
                // Underlying type is known, and as such, we can generate a type-accurate (somewhat) enum representation
                let underlying_type_name = self.generate_primitive_type(&known_underlying_type);
                type_inner_field = quote! { _underlying_value: #underlying_type_name };
                all_type_implementations.push(quote! {
                    impl #parameter_declaration #type_name #parameter_list {
                        pub fn from_underlying_type(underlying_type: #underlying_type_name) -> Self { Self{ _underlying_value: underlying_type, ..Self::default() } }
                        pub fn to_underlying_type(self) -> #underlying_type_name { self._underlying_value }
                        pub fn to_raw_discriminant(self) -> u64 { use gospel_runtime::core_type_definitions::EnumUnderlyingType; self.to_underlying_type().to_raw_discriminant() }
                        pub fn from_raw_discriminant(raw_discriminant: u64) -> Self { use gospel_runtime::core_type_definitions::EnumUnderlyingType; Self::from_underlying_type(#underlying_type_name::from_raw_discriminant(raw_discriminant)) }
                    }
                });
                all_type_implementations.push(quote! {
                     impl #parameter_declaration gospel_runtime::external_type_model::ExternallyConvertible for #type_name #parameter_list {
                        fn read_external<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>) -> anyhow::Result<Self> {
                            Ok(Self::from_underlying_type(#underlying_type_name::read_external(ptr)?))
                        }
                        fn write_external<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                            #underlying_type_name::write_external(ptr, value.to_underlying_type())
                        }
                        fn read_external_slice<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                            let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut #underlying_type_name, buffer.len()) };
                            #underlying_type_name::read_external_slice(ptr, underlying_type_buffer)
                        }
                        fn write_external_slice<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                            let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const #underlying_type_name, buffer.len()) };
                            #underlying_type_name::write_external_slice(ptr, underlying_type_buffer)
                        }
                    }
                });
            } else {
                // Underlying type is not known, and as such, we have to use the widest type available to represent the possible discriminant
                // We cannot generate enums as DSTs in external type model due to the fact that we cannot allocate new memory to represent constant values
                type_inner_field = quote! { _raw_discriminant_value: u64 };
                all_type_implementations.push(quote! {
                    impl #parameter_declaration #type_name #parameter_list {
                        pub fn to_raw_discriminant(self) -> u64 { self._raw_discriminant_value }
                        pub fn from_raw_discriminant(raw_discriminant: u64) -> Self { Self{ _raw_discriminant_value: raw_discriminant, ..Self::default() } }
                    }
                });
                all_type_implementations.push(quote! {
                     impl #parameter_declaration gospel_runtime::external_type_model::ExternallyConvertible for #type_name #parameter_list {
                        fn read_external<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>) -> anyhow::Result<Self> {
                            use gospel_runtime::core_type_definitions::StaticTypeTag;
                            use std::ops::Deref;
                            let enum_static_type_index = Self::store_type_descriptor_to_namespace(ptr.memory.deref());
                            let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(ptr.clone(), enum_static_type_index);
                            Ok(Self::from_raw_discriminant(enum_dyn_ptr.read_integral_type()?))
                        }
                        fn write_external<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, value: Self) -> anyhow::Result<()> {
                            use gospel_runtime::core_type_definitions::StaticTypeTag;
                            use std::ops::Deref;
                            let enum_static_type_index = Self::store_type_descriptor_to_namespace(ptr.memory.deref());
                            let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(ptr.clone(), enum_static_type_index);
                            enum_dyn_ptr.write_integral_type(value.to_raw_discriminant())
                        }
                        fn read_external_slice<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &mut [Self]) -> anyhow::Result<()> {
                            use gospel_runtime::core_type_definitions::StaticTypeTag;
                            use std::ops::Deref;
                            let enum_static_type_index = Self::store_type_descriptor_to_namespace(ptr.memory.deref());
                            let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(ptr.clone(), enum_static_type_index);
                            // SAFETY: This is safe as long as type has a transparent representation
                            let mut underlying_type_buffer = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(buffer.as_mut_ptr() as *mut u64, buffer.len()) };
                            enum_dyn_ptr.read_integral_type_slice(underlying_type_buffer)
                        }
                        fn write_external_slice<M: gospel_runtime::external_memory::Memory + gospel_runtime::external_type_model::TypeNamespace>(ptr: &gospel_runtime::external_memory::OpaquePtr<M>, buffer: &[Self]) -> anyhow::Result<()> {
                            use gospel_runtime::core_type_definitions::StaticTypeTag;
                            use std::ops::Deref;
                            let enum_static_type_index = Self::store_type_descriptor_to_namespace(ptr.memory.deref());
                            let enum_dyn_ptr = gospel_runtime::external_type_model::DynPtr::from_raw_ptr(ptr.clone(), enum_static_type_index);
                            // SAFETY: This is safe as long as type has a transparent representation
                            let underlying_type_buffer = unsafe { &*std::ptr::slice_from_raw_parts(buffer.as_ptr() as *const u64, buffer.len()) };
                            enum_dyn_ptr.write_integral_type_slice(underlying_type_buffer)
                        }
                    }
                });
            }
            // Enum types generated by external bindings are always value types, so we add the value type attributes to them
            type_additional_attributes = Some(quote! {
                #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
                #[repr(transparent)]
            });
        } else {
            if let Some(known_underlying_type) = underlying_type {
                // Underlying type is known, and as such, we can generate a sized enum value type
                let underlying_type_name = self.generate_primitive_type(&known_underlying_type);
                type_inner_field = quote! { _underlying_value: #underlying_type_name };
                all_type_implementations.push(quote! {
                    impl #parameter_declaration #type_name #parameter_list {
                        pub fn from_underlying_type(underlying_type: #underlying_type_name) -> Self { Self{ _underlying_value: underlying_type, ..Self::default() } }
                        pub fn to_underlying_type(self) -> #underlying_type_name { self._underlying_value }
                        pub fn sized_to_raw_discriminant(self) -> u64 { use gospel_runtime::core_type_definitions::EnumUnderlyingType; self.to_underlying_type().to_raw_discriminant() }
                        pub fn sized_from_raw_discriminant(raw_discriminant: u64) -> Self { use gospel_runtime::core_type_definitions::EnumUnderlyingType; Self::from_underlying_type(#underlying_type_name::from_raw_discriminant(raw_discriminant)) }
                        pub fn boxed_to_raw_discriminant(&self) -> u64 { self.sized_to_raw_discriminant() }
                        pub fn boxed_from_raw_discriminant<A : std::alloc:::Allocator>(raw_discriminant: u64, alloc: A) -> Box<Self, A> { Box::<Self, A>::new_in(Self::sized_from_raw_discriminant(raw_discriminant), alloc) }
                    }
                });
                type_additional_attributes = Some(quote! {
                    #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
                    #[repr(transparent)]
                });
            } else {
                // Underlying type is unknown, so we have to generate the enum as a dynamically sized type
                let type_universe = Ident::new(&self.type_universe_full_name, Span::call_site());
                type_inner_field = quote! { _private_bytes: [u8] };
                all_type_implementations.push(quote! {
                    impl #parameter_declaration gospel_runtime::local_type_model::ImplicitPtrMetadata for #type_name #parameter_list {
                        fn create_implicit_metadata() -> Self::Metadata {
                            use generic_statics::{define_namespace, Namespace};
                            define_namespace!(TypeDescriptor);
                            let (type_size, _) = TypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().get_type_size_and_alignment();
                            type_size
                        }
                        fn static_align_of_val() -> usize {
                            use generic_statics::{define_namespace, Namespace};
                            define_namespace!(TypeDescriptor);
                            let (_, type_alignment) = TypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().get_type_size_and_alignment();
                            type_alignment
                        }
                    }
                    unsafe impl #parameter_declaration std::clone::CloneToUninit for #type_name #parameter_list {
                        unsafe fn clone_to_uninit(&self, dest: *mut u8) {
                            dest.copy_from(self._private_bytes.as_ptr(), Self::static_size_of_val());
                        }
                    }
                    unsafe impl #parameter_declaration gospel_runtime::local_type_model::DefaultConstructAtUninit for #type_name #parameter_list {
                        unsafe fn default_construct_at(dest: *mut u8) {
                            dest.write_bytes(0, Self::static_size_of_val());
                        }
                    }
                    impl #parameter_declaration #type_name #parameter_list {
                        pub fn boxed_to_raw_discriminant(&self) -> u64 {
                            use generic_statics::{define_namespace, Namespace};
                            define_namespace!(EnumTypeDescriptor);
                            EnumTypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().read_boxed_enum_value(self)
                        }
                        pub fn boxed_from_raw_discriminant<A : std::alloc:::Allocator>(raw_discriminant: u64, alloc: A) -> Box<Self, A> {
                            use generic_statics::{define_namespace, Namespace};
                            define_namespace!(EnumTypeDescriptor);
                            EnumTypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().create_boxed_enum_value::<A>(raw_discriminant, alloc)
                        }
                    }
                });
            }
        }

        Ok(quote! {
            #type_doc_comment
            #type_additional_attributes
            pub struct #type_name #parameter_declaration {
                #phantom_data_list
                #type_inner_field
            }
            #(#all_type_implementations)*
            impl #parameter_declaration #type_name #parameter_list {
                #(#generated_constants)*
            }
        })
    }
    fn generate_fallback_type_definition(&self, raw_type_name: &str) -> TokenStream {
        let type_name = Ident::new(&Self::generate_short_type_name(&raw_type_name), Span::call_site());
        quote! { type #type_name = (); }
    }
    pub(crate) fn generate_bindings_file(self) -> anyhow::Result<String> {
        let mut type_definitions: Vec<TokenStream> = Vec::new();
        for type_definition in &self.module_context.types_to_generate {
            if let Some(type_index) = type_definition.type_index {
                let base_type_index = self.module_context.run_context.base_type_index(type_index);
                let type_container = self.module_context.run_context.type_container_by_index(base_type_index);

                if let Type::UDT(user_defined_type) = &type_container.wrapped_type {
                    // Generate user defined type definition
                    let result_type_definition = self.generate_udt_definition(user_defined_type, type_container, type_definition)?;
                    type_definitions.push(result_type_definition.clone());
                } else if let Type::Enum(enum_type) = &type_container.wrapped_type {
                    let result_type_definition = self.generate_enum_definition(enum_type, type_container, type_definition)?;
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
        let imported_macros = match self.bindings_type {
            ModuleBindingsType::External => quote! { #[macro_use(gsb_codegen_implement_external_udt_field, gsb_codegen_implement_external_enum_constant)] },
            ModuleBindingsType::Local => quote! { #[macro_use(gsb_codegen_implement_local_udt_field, gsb_codegen_implement_local_enum_constant)] }
        };
        let result_file_token_stream = quote! {
            #imported_macros
            #[allow(unused)]
            extern crate gospel_runtime;

            #[allow(warnings, unused)]
            mod #bindings_mod_name {
                #(#bindings_extra_definitions)*
                #(#type_definitions)*
            }
        };
        let parsed_file = parse2::<File>(result_file_token_stream.clone()).map_err(|x| {
            let contents_dump_location = absolute(temp_dir().join(PathBuf::from(format!("bindings_source_text_{}.rs", Uuid::new_v4())))).unwrap();
            write(&contents_dump_location, result_file_token_stream.to_string()).unwrap();
            anyhow!("Failed to parse generated file: {} (contents dumped to {})", x, contents_dump_location.display())
        })?;
        Ok(prettyplease::unparse(&parsed_file))
    }
}
