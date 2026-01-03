use crate::module_processor::{BindingsTypeDefinition, ResolvedBindingsModuleContext};
use crate::ModuleBindingsType;
use anyhow::{anyhow, bail};
use convert_case::{Case, Casing};
use gospel_compiler::ast::ExpressionValueType;
use gospel_compiler::backend::CompilerFunctionSignature;
use gospel_compiler::core_attributes::{is_trivially_constructible, is_trivially_copyable};
use gospel_typelib::type_model::{EnumType, FunctionDeclaration, PrimitiveType, Type, TypeGraphLike, UserDefinedType, UserDefinedTypeMember};
use gospel_vm::vm::{GospelVMTypeContainer, GospelVMValue};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::env::temp_dir;
use std::fs::write;
use std::path::{absolute, PathBuf};
use syn::{parse_str, File};
use uuid::Uuid;

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

struct FunctionParameterTypeTokens {
    declaration: TokenStream,
    type_descriptor: TokenStream,
    value_as_mut_u8_ptr: TokenStream,
    value_parameter_passed_as_reference: bool,
    references_allocator_type: bool,
}

#[derive(Default)]
struct FunctionReturnValueTokens {
    return_value_type: Option<TokenStream>,
    return_value_static_type_tag: Option<TokenStream>,
    before_return_value_statement: Option<TokenStream>,
    return_value_storage_initializer: Option<TokenStream>,
    return_expression: Option<TokenStream>,
    needs_allocator_instance: bool,
    return_value_through_storage: bool,
}

#[derive(Clone, Default)]
struct FieldPrototypeData {
    field_name: String,
    field_type_index: Option<usize>,
}

#[derive(Clone, Default)]
struct VirtualFunctionPrototypeData {
    virtual_function: FunctionDeclaration,
    unresolved_return_type: bool,
    variable_argument_count: bool,
    nameless_parameter_indices: HashSet<usize>,
    unresolved_parameter_type_indices: HashSet<usize>,
}

impl CodeGenerationContext {
    fn generate_primitive_type(&self, primitive_type: &PrimitiveType) -> TokenStream {
        match primitive_type {
            PrimitiveType::Void => quote!{ () },
            PrimitiveType::Char => quote!{ i8 },
            PrimitiveType::UnsignedChar => quote!{ u8 },
            PrimitiveType::WideChar => match self.bindings_type {
                ModuleBindingsType::Local => quote! { gospel_runtime::local_type_model::PlatformWideChar },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalWideChar },
            },
            PrimitiveType::ShortInt => quote!{ i16 },
            PrimitiveType::UnsignedShortInt => quote!{ u16 },
            PrimitiveType::Int => quote!{ i32 },
            PrimitiveType::UnsignedInt => quote!{ u32 },
            PrimitiveType::Float => quote!{ f32 },
            PrimitiveType::Double => quote!{ f64 },
            PrimitiveType::Bool => quote!{ bool },
            PrimitiveType::LongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! { gospel_runtime::local_type_model::PlatformLongInt },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalLongInt },
            },
            PrimitiveType::UnsignedLongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::PlatformUnsignedLongInt },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalUnsignedLongInt },
            },
            PrimitiveType::LongLongInt => quote!{ i64 },
            PrimitiveType::UnsignedLongLongInt => quote!{ u64 },
            PrimitiveType::Char8 => quote!{ gospel_runtime::core_type_definitions::Char8 },
            PrimitiveType::Char16 => quote!{ gospel_runtime::core_type_definitions::Char16 },
            PrimitiveType::Char32 => quote!{ gospel_runtime::core_type_definitions::Char32 },
        }
    }
    fn cast_primitive_type_to_u64(&self, primitive_type: PrimitiveType, primitive_value: TokenStream) -> anyhow::Result<TokenStream> {
        Ok(match primitive_type {
            PrimitiveType::Void => bail!("Void type is sizeless"),
            PrimitiveType::Char => quote!{ #primitive_value as u64 },
            PrimitiveType::UnsignedChar => quote!{ #primitive_value as u64 },
            PrimitiveType::WideChar => quote! { #primitive_value.0 as u64 },
            PrimitiveType::ShortInt => quote!{ #primitive_value as u64 },
            PrimitiveType::UnsignedShortInt => quote!{ #primitive_value as u64 },
            PrimitiveType::Int => quote!{ #primitive_value as u64 },
            PrimitiveType::UnsignedInt => quote!{ #primitive_value as u64 },
            PrimitiveType::Float => quote!{ #primitive_value.to_bits() as u64 },
            PrimitiveType::Double => quote!{ #primitive_value.to_bits() as u64 },
            PrimitiveType::Bool => quote!{ #primitive_value as u64 },
            PrimitiveType::LongInt => quote! { #primitive_value.0 as u64 },
            PrimitiveType::UnsignedLongInt => quote! { #primitive_value.0 as u64 },
            PrimitiveType::LongLongInt => quote!{ #primitive_value as u64 },
            PrimitiveType::UnsignedLongLongInt => quote!{ #primitive_value as u64 },
            PrimitiveType::Char8 => quote!{ #primitive_value.0 as u64 },
            PrimitiveType::Char16 => quote!{ #primitive_value.0 as u64 },
            PrimitiveType::Char32 => quote!{ #primitive_value.0 as u64 },
        })
    }
    fn cast_u64_to_primitive_type(&self, primitive_type: PrimitiveType, u64_value: TokenStream) -> anyhow::Result<TokenStream> {
        Ok(match primitive_type {
            PrimitiveType::Void => bail!("Void type is sizeless"),
            PrimitiveType::Char => quote!{ #u64_value as i8 },
            PrimitiveType::UnsignedChar => quote!{ #u64_value as u8 },
            PrimitiveType::WideChar => match self.bindings_type {
                ModuleBindingsType::Local => quote! { gospel_runtime::local_type_model::PlatformWideChar(#u64_value as gospel_runtime::local_type_model::PlatformWideCharUnderlyingType) },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalWideChar(#u64_value as u32) },
            },
            PrimitiveType::ShortInt => quote!{ #u64_value as i16 },
            PrimitiveType::UnsignedShortInt => quote!{ #u64_value as u16 },
            PrimitiveType::Int => quote!{ #u64_value as i32 },
            PrimitiveType::UnsignedInt => quote!{ #u64_value as u32 },
            PrimitiveType::Float => quote!{ f32::from_bits(#u64_value as u32) },
            PrimitiveType::Double => quote!{ f64::from_bits(#u64_value as u64) },
            PrimitiveType::Bool => quote!{ if #u64_value == 0 { false } else { true } },
            PrimitiveType::LongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! { gospel_runtime::local_type_model::PlatformLongInt(#u64_value as gospel_runtime::local_type_model::PlatformLongIntUnderlyingType) },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalLongInt(#u64_value as i64) },
            },
            PrimitiveType::UnsignedLongInt => match self.bindings_type {
                ModuleBindingsType::Local => quote! { gospel_runtime::local_type_model::PlatformUnsignedLongInt(#u64_value as gospel_runtime::local_type_model::PlatformUnsignedLongIntUnderlyingType) },
                ModuleBindingsType::External => quote! { gospel_runtime::external_type_model::ExternalUnsignedLongInt(#u64_value as u64) },
            },
            PrimitiveType::LongLongInt => quote!{ #u64_value as i64 },
            PrimitiveType::UnsignedLongLongInt => quote!{ #u64_value as u64 },
            PrimitiveType::Char8 => quote!{ gospel_runtime::core_type_definitions::Char8(#u64_value as u8) },
            PrimitiveType::Char16 => quote!{ gospel_runtime::core_type_definitions::Char16(#u64_value as u16) },
            PrimitiveType::Char32 => quote!{ gospel_runtime::core_type_definitions::Char32(#u64_value as u32) },
        })
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
        let documentation_attributes: Vec<TokenStream> = type_definition.function_declaration.as_ref().unwrap().metadata.get(doc_metadata)?.iter()
            .filter(|x| !x.is_empty())
            .map(|doc_comment_line| quote! { #[doc = #doc_comment_line] })
            .collect();
        if documentation_attributes.is_empty() { None } else { Some(quote!{ #(#documentation_attributes)* }) }
    }
    fn generate_type_universe_full_name(&self) -> TokenStream {
        let partial_idents: Vec<Ident> = self.type_universe_full_name.split("::").map(|x| Ident::new(x, Span::call_site())).collect();
        quote! { #(#partial_idents)::* }
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
            GospelVMValue::TypeReference(type_index) => Ok(self.generate_type_name(*type_index)?),
            GospelVMValue::Primitive(primitive_value) => Ok(self.generate_primitive_value_as_type(*primitive_value)),
            _ => bail!("Unsupported type argument value type: {}", value)
        }
    }
    fn generate_type_name(&self, type_index: usize) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);

        Ok(match type_definition {
            Type::Array(array_type) => {
                let element_type = self.generate_type_name(array_type.element_type_index)?;
                let array_length = self.generate_primitive_value_as_type(array_type.array_length as u64);
                match self.bindings_type {
                    ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::StaticArray::<#element_type, #array_length>},
                    ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::StaticArray::<#element_type, #array_length>},
                }
            },
            Type::Pointer(pointer_type) => {
                let pointee_type = self.generate_type_name(pointer_type.pointee_type_index)?;
                if pointer_type.is_reference {
                    match self.bindings_type {
                        ModuleBindingsType::Local => quote! {gospel_runtime::local_type_model::CRef::<#pointee_type>},
                        ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::Ref::<M, #pointee_type>},
                    }
                } else {
                    match self.bindings_type {
                        ModuleBindingsType::Local => quote! {Option::<gospel_runtime::local_type_model::CRef::<#pointee_type>>},
                        ModuleBindingsType::External => quote! {gospel_runtime::external_type_model::Ptr::<M, #pointee_type>},
                    }
                }
            }
            Type::CVQualified(cv_qualified_type) => {
                self.generate_type_name(cv_qualified_type.base_type_index)?
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
                if let Some(enum_name) = &enum_type.name && let Some(source_crate_name) = self.module_context.type_source_crate_lookup.get(enum_name) {
                    // Try to generate as an explicit enum definition within source crate first
                    let full_type_name = self.generate_type_qualified_name(source_crate_name, enum_name);
                    quote! { #full_type_name }
                } else if let Some(underlying_type) = self.calculate_enum_underlying_type(base_type_index)? {
                    // Fall back to the underlying type if there is no mapping to the type source crate
                    self.generate_primitive_type(&underlying_type)
                } else {
                    quote! { () }
                }
            }
        })
    }
    fn calculate_bindings_type_size_if_possible(&self, type_index: usize) -> anyhow::Result<Option<usize>> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        Ok(match type_definition {
            Type::Array(_) => None,
            Type::Pointer(_) => Some(self.module_context.run_context.target_triplet().unwrap().address_width()),
            Type::CVQualified(cv_qualified_type) => self.calculate_bindings_type_size_if_possible(cv_qualified_type.base_type_index)?,
            Type::Primitive(primitive_type) => if primitive_type.is_sizeless() { None } else { Some(primitive_type.size_and_alignment(self.module_context.run_context.target_triplet().unwrap())?) },
            Type::Function(_) => bail!("Function type is sizeless"),
            Type::UDT(_) => None,
            Type::Enum(_) => if let Some(underlying_type) = self.calculate_enum_underlying_type(base_type_index)? { Some(underlying_type.size_and_alignment(self.module_context.run_context.target_triplet().unwrap())?) } else { None },
        })
    }
    fn generate_bindings_type_cast_to_u64(&self, type_index: usize, value_name: TokenStream) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        Ok(match type_definition {
            Type::Array(_) => bail!("Arrays cannot be cast to u64"),
            Type::Pointer(_) => bail!("Did not expect Pointer type here"),
            Type::CVQualified(_) => bail!("Did not expect CVQualified type here"),
            Type::Primitive(primitive_type) => self.cast_primitive_type_to_u64(*primitive_type, value_name)?,
            Type::Function(_) => bail!("Function type is sizeless"),
            Type::UDT(_) => bail!("UDTs cannot be cast to u64"),
            Type::Enum(_) => {
                let underlying_value_name = quote!{ #value_name.to_underlying_type() };
                self.cast_primitive_type_to_u64(self.calculate_enum_underlying_type(base_type_index)?.ok_or_else(|| anyhow!("Enum underlying type not statically known"))?, underlying_value_name)?
            },
        })
    }
    fn generate_bindings_type_create_from_u64(&self, type_index: usize, u64_value_name: TokenStream) -> anyhow::Result<TokenStream> {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        Ok(match type_definition {
            Type::Array(_) => bail!("Arrays cannot be created from u64"),
            Type::Pointer(_) => bail!("Did not expect Pointer type here"),
            Type::CVQualified(_) => bail!("Did not expect CVQualified type here"),
            Type::Primitive(primitive_type) => self.cast_u64_to_primitive_type(*primitive_type, u64_value_name)?,
            Type::Function(_) => bail!("Function type is sizeless"),
            Type::UDT(_) => bail!("UDTs cannot be created from u64"),
            Type::Enum(_) => self.cast_u64_to_primitive_type(self.calculate_enum_underlying_type(base_type_index)?.ok_or_else(|| anyhow!("Enum underlying type not statically known"))?, u64_value_name)?,
        })
    }
    fn generate_function_parameter_name(optional_parameter_name: &Option<String>, parameter_index: usize) -> Ident {
        let raw_parameter_name = if let Some(parameter_name) = optional_parameter_name {
            Self::convert_field_name_to_snake_case(parameter_name)
        } else { format!("param_{}", parameter_index) };
        Ident::new(&raw_parameter_name, Span::call_site())
    }
    fn generate_function_parameter_type(&self, parameter_type_index: usize, parameter_name: &Ident) -> anyhow::Result<FunctionParameterTypeTokens> {
        let base_type_index = self.module_context.run_context.base_type_index(parameter_type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        let parameter_type_tag = self.generate_type_name(base_type_index)?;

        if let Type::Pointer(pointer_type) = type_definition {
            // Unwrap pointee type as CV qualified type if possible to determine whenever pointee type is a constant type
            let (pointee_type_index, is_pointee_const) = if let Type::CVQualified(cv_qualified_pointee_type) = pointer_type.pointee_type(&self.module_context.run_context) {
                (cv_qualified_pointee_type.base_type_index, cv_qualified_pointee_type.constant)
            } else { (pointer_type.pointee_type_index, false) };

            // Generate as Rust reference type whenever possible to make working with call sites easier, and if it is a pointer generate it as a raw pointer
            let pointee_type_name = self.generate_type_name(pointee_type_index)?;
            if pointer_type.is_reference {
                if is_pointee_const {
                    Ok(FunctionParameterTypeTokens{
                        declaration: quote!{ #parameter_name: &#pointee_type_name },
                        type_descriptor: quote!{ #parameter_type_tag },
                        value_as_mut_u8_ptr: quote!{ #parameter_name as *const #pointee_type_name as *mut u8 },
                        value_parameter_passed_as_reference: false,
                        references_allocator_type: false,
                    })
                } else {
                    Ok(FunctionParameterTypeTokens{
                        declaration: quote!{ #parameter_name: &mut #pointee_type_name },
                        type_descriptor: quote!{ #parameter_type_tag },
                        value_as_mut_u8_ptr: quote!{ #parameter_name as *mut #pointee_type_name as *mut u8 },
                        value_parameter_passed_as_reference: false,
                        references_allocator_type: false,
                    })
                }
            } else {
                if is_pointee_const {
                    Ok(FunctionParameterTypeTokens{
                        declaration: quote!{ #parameter_name: *const #pointee_type_name },
                        type_descriptor: quote!{ #parameter_type_tag },
                        value_as_mut_u8_ptr: quote!{ #parameter_name as *mut u8 },
                        value_parameter_passed_as_reference: false,
                        references_allocator_type: false,
                    })
                } else {
                    Ok(FunctionParameterTypeTokens{
                        declaration: quote!{ #parameter_name: *mut #pointee_type_name },
                        type_descriptor: quote!{ #parameter_type_tag },
                        value_as_mut_u8_ptr: quote!{ #parameter_name as *mut u8 },
                        value_parameter_passed_as_reference: false,
                        references_allocator_type: false,
                    })
                }
            }
        } else if let Some(known_type_size_bytes) = self.calculate_bindings_type_size_if_possible(base_type_index)? {
            // Bindings type static size is known (e.g. this is a primitive type or an enumeration type with a known underlying size), we can generate the parameter directly
            if known_type_size_bytes <= size_of::<usize>() {
                // Type is small enough to be passed by value directly
                let type_value_as_u64 = self.generate_bindings_type_cast_to_u64(base_type_index, quote!{ #parameter_name })?;
                Ok(FunctionParameterTypeTokens{
                    declaration: quote!{ #parameter_name: #parameter_type_tag },
                    type_descriptor: quote!{ #parameter_type_tag },
                    value_as_mut_u8_ptr: quote!{ std::ptr::without_provenance_mut::<u8>(#type_value_as_u64 as usize) },
                    value_parameter_passed_as_reference: false,
                    references_allocator_type: false,
                })
            } else {
                // Type is too big to be passed by value to the call thunk, so we pass it as a reference
                Ok(FunctionParameterTypeTokens{
                    declaration: quote!{ #parameter_name: mut #parameter_type_tag },
                    type_descriptor: quote!{ #parameter_type_tag },
                    value_as_mut_u8_ptr: quote!{ &mut #parameter_name as *mut #parameter_type_tag as *mut u8 },
                    value_parameter_passed_as_reference: true,
                    references_allocator_type: false,
                })
            }
        } else {
            // Static size is not known, but this argument is passed by value, so we have to wrap it in a box and pass it as a reference
            Ok(FunctionParameterTypeTokens{
                declaration: quote!{ #parameter_name: mut Box<#parameter_type_tag, A> },
                type_descriptor: quote!{ #parameter_type_tag },
                value_as_mut_u8_ptr: quote!{ parameter_name.as_mut() as *mut #parameter_type_tag as *mut u8 },
                value_parameter_passed_as_reference: true,
                references_allocator_type: true,
            })
        }
    }
    fn generate_function_return_value(&self, type_universe: &TokenStream, maybe_return_value_type_index: Option<usize>, source_function_name: &str) -> anyhow::Result<FunctionReturnValueTokens> {
        if let Some(return_value_type_index) = maybe_return_value_type_index {
            // Return value type is known statically. We can either return the value directly if the size is known, and it fits in a pointer, or return it as a box
            let base_type_index = self.module_context.run_context.base_type_index(return_value_type_index);
            let type_definition = self.module_context.run_context.type_by_index(base_type_index);

            if type_definition != &Type::Primitive(PrimitiveType::Void) {
                // This function returns a non-void type, see if we can calculate its size and fit it in a pointer
                let return_value_type = self.generate_type_name(base_type_index)?;

                if let Type::Pointer(pointer_type) = type_definition {
                    // Type is a pointer, return by value and convert the pointer to the wrapped type while preserving the provenance
                    let pointee_type_name = self.generate_type_name(pointer_type.pointee_type_index)?;
                    let base_c_reference_type = quote! { gospel_runtime::local_type_model::CRef::<#pointee_type_name> };
                    let pointer_return_value_type = if pointer_type.is_reference { base_c_reference_type.clone() } else { quote! { Option<#base_c_reference_type> } };
                    let construct_return_value_expression = if pointer_type.is_reference { quote! { #base_c_reference_type::from_raw_ptr(return_value_direct) } } else {
                        quote! { #base_c_reference_type::from_raw_ptr_nullable(return_value_direct) } };

                    Ok(FunctionReturnValueTokens{
                        return_value_type: Some(pointer_return_value_type),
                        return_value_static_type_tag: Some(return_value_type),
                        before_return_value_statement: None,
                        return_value_storage_initializer: None,
                        return_expression: Some(construct_return_value_expression),
                        needs_allocator_instance: false,
                        return_value_through_storage: false,
                    })
                } else if let Some(known_type_size_bytes) = self.calculate_bindings_type_size_if_possible(base_type_index)? {
                    if known_type_size_bytes <= size_of::<usize>() {
                        // Type is small enough to be marshalled as a pointer, in which case return value storage is not needed
                        Ok(FunctionReturnValueTokens{
                            return_value_type: Some(return_value_type.clone()),
                            return_value_static_type_tag: Some(return_value_type),
                            before_return_value_statement: None,
                            return_value_storage_initializer: None,
                            return_expression: Some(self.generate_bindings_type_create_from_u64(base_type_index, quote! { return_value_direct.addr() as u64 })?),
                            needs_allocator_instance: false,
                            return_value_through_storage: false,
                        })
                    } else {
                        // Type has a known size in bindings, but is too big to be marshalled as a pointer. We can allocate static storage slot for it
                        // on the stack directly, pass it to the function to write to, and then return
                        Ok(FunctionReturnValueTokens{
                            return_value_type: Some(return_value_type.clone()),
                            return_value_static_type_tag: Some(return_value_type.clone()),
                            before_return_value_statement: Some(quote! { let mut uninit_return_value = std::mem::MaybeUninit::<#return_value_type>::uninit(); }),
                            return_value_storage_initializer: Some(quote! { uninit_return_value.as_mut_ptr() }),
                            return_expression: Some(quote! { unsafe { uninit_return_value.assume_init() } }),
                            needs_allocator_instance: false,
                            return_value_through_storage: true,
                        })
                    }
                } else {
                    // Type does not have a known size, we have to construct a box to hold its value
                    Ok(FunctionReturnValueTokens{
                        return_value_type: Some(quote! { std::boxed::Box<#return_value_type, A> }),
                        return_value_static_type_tag: Some(return_value_type.clone()),
                        before_return_value_statement: None,
                        return_value_storage_initializer: Some(quote! { gospel_runtime::local_type_model::allocate_uninitialized::<#return_value_type, A>(&alloc) }),
                        return_expression: Some(quote! { unsafe { std::boxed::Box::<#return_value_type, A>::from_raw_in(#return_value_type::from_raw_ptr_mut(return_value_storage), alloc) } }),
                        needs_allocator_instance: true,
                        return_value_through_storage: true,
                    })
                }
            } else {
                // This function returns void, so return completely empty tokens struct
                Ok(FunctionReturnValueTokens::default())
            }
        } else {
            // Return value type is unknown statically. Unfortunately we do not know how to destruct dynamic values right now (e.g. there is no DynBox),
            // so we will have to allocate the memory and then return the raw pointer to it to the user
            // We also have to wrap it in an Option, since the function might end up not returning anything at all
            let calc_type_size_and_alignment = quote! { let (type_size, type_alignment) = #type_universe::type_layout_cache().lock().unwrap().get_type_size_and_alignment_cached(#type_universe::type_graph(), return_type_index); };
            let storage_allocate_expression = quote! { alloc.allocate(std::alloc::Layout::from_size_align(type_size, type_alignment).unwrap()).unwrap().as_ptr() as *mut u8 };
            let make_dyn_mut_expression = quote! { gospel_runtime::local_type_model::DynMut::<#type_universe>::from_raw_parts(return_value_storage, return_type_index) };

            Ok(FunctionReturnValueTokens{
                return_value_type: Some(quote! { Option<gospel_runtime::local_type_model::DynMut<#type_universe>> }),
                return_value_static_type_tag: None,
                before_return_value_statement: Some(quote! { let maybe_return_type_index = call_descriptor.get_non_void_return_value_type(#source_function_name); }),
                return_value_storage_initializer: Some(quote! { if let Some(return_type_index) = maybe_return_type_index { #calc_type_size_and_alignment; #storage_allocate_expression } else { std::ptr::null_mut() } }),
                return_expression: Some(quote!{ if let Some(return_type_index) = maybe_return_type_index { Some(unsafe { #make_dyn_mut_expression }) } else { None } }),
                needs_allocator_instance: true,
                return_value_through_storage: true,
            })
        }
    }
    fn is_opaque_type_index(&self, type_index: usize) -> bool {
        let base_type_index = self.module_context.run_context.base_type_index(type_index);
        let type_definition = self.module_context.run_context.type_by_index(base_type_index);
        if let Type::Primitive(primitive_type) = type_definition {
            *primitive_type == PrimitiveType::Void
        } else { false }
    }
    fn generate_type_field_definition(&self, source_file_name: &str, field_name: &Ident, maybe_field_type_index: Option<usize>, is_prototype_field: bool, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let field_doc_comment = Self::generate_doc_comment(type_definition, &format!("{}$doc", source_file_name));
        Ok(if let Some(field_type_index) = maybe_field_type_index && !self.is_opaque_type_index(field_type_index) {
            let field_type = self.generate_type_name(field_type_index)?;
            match self.bindings_type {
                ModuleBindingsType::External => {
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, optional, { #field_doc_comment }, #field_type); }
                    } else {
                        quote! { gsb_codegen_implement_external_udt_field!(#field_name, #source_file_name, required, { #field_doc_comment }, #field_type); }
                    }
                }
                ModuleBindingsType::Local => {
                    let type_universe = self.generate_type_universe_full_name();
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
                    let type_universe = self.generate_type_universe_full_name();
                    if is_prototype_field {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, optional, { #field_doc_comment }); }
                    } else {
                        quote! { gsb_codegen_implement_local_udt_field!(#field_name, #source_file_name, #type_universe, required, { #field_doc_comment }); }
                    }
                }
            }
        })
    }
    fn generate_type_virtual_function_definition(&self, virtual_function_prototype: &VirtualFunctionPrototypeData, is_prototype_virtual_function: bool, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let mut parameter_declarations: Vec<TokenStream> = Vec::new();
        let mut parameter_ptr_values: Vec<TokenStream> = Vec::new();
        let mut parameter_pass_by_reference: Vec<TokenStream> = Vec::new();
        let mut parameter_type_indices: Vec<TokenStream> = Vec::new();
        let mut has_any_dynamic_parameters: bool = false;
        let mut any_parameters_need_allocator_type: bool = false;
        let mut any_parameters_need_allocator_instance: bool = false;

        let function_name_string_sneak_case = Self::convert_field_name_to_snake_case(&virtual_function_prototype.virtual_function.name);
        let virtual_function_name = &Ident::new(&function_name_string_sneak_case, Span::call_site());

        let function_doc_comment = Self::generate_doc_comment(type_definition, &format!("{}$doc", &virtual_function_prototype.virtual_function.name));
        let type_universe = self.generate_type_universe_full_name();

        let return_value_tokens = self.generate_function_return_value(&type_universe, if virtual_function_prototype.unresolved_return_type { None } else {
            Some(virtual_function_prototype.virtual_function.return_value_type_index)
        }, &virtual_function_prototype.virtual_function.name)?;
        any_parameters_need_allocator_instance |= return_value_tokens.needs_allocator_instance;

        for parameter_index in 0..virtual_function_prototype.virtual_function.parameters.len() {
            let parameter_name = Self::generate_function_parameter_name(&virtual_function_prototype.virtual_function.parameters[parameter_index].parameter_name, parameter_index);
            if virtual_function_prototype.unresolved_parameter_type_indices.contains(&parameter_index) {
                // This parameter does not have a known type, pass it as a reference with dynamic type
                parameter_declarations.push(quote!{ #parameter_name: gospel_runtime::local_type_model::DynMut<#type_universe> });
                parameter_ptr_values.push(quote!{ #parameter_name.as_raw_ptr() });
                parameter_pass_by_reference.push(quote!{ true });
                parameter_type_indices.push(quote!{ #parameter_name.type_index() });
                has_any_dynamic_parameters = true;
            } else {
                // We have a known type for this parameter, so just generate it normally
                let parameter_data = self.generate_function_parameter_type(virtual_function_prototype.virtual_function.parameters[parameter_index].parameter_type_index, &parameter_name)?;
                let pass_by_reference = parameter_data.value_parameter_passed_as_reference;
                let static_type_tag_class = parameter_data.type_descriptor;

                parameter_declarations.push(parameter_data.declaration);
                parameter_ptr_values.push(parameter_data.value_as_mut_u8_ptr);
                parameter_pass_by_reference.push(quote!{ #pass_by_reference });
                parameter_type_indices.push(quote!{ #static_type_tag_class::store_type_descriptor_to_universe::<#type_universe>() });
                any_parameters_need_allocator_type |= parameter_data.references_allocator_type;
            }
        }

        if virtual_function_prototype.variable_argument_count {
            parameter_declarations.push(quote!{ extra_params: &Vec<gospel_runtime::local_type_model::DynMut<#type_universe>> });
            has_any_dynamic_parameters = true;
        }
        if any_parameters_need_allocator_instance {
            parameter_declarations.insert(0, quote! { alloc: A });
            any_parameters_need_allocator_type = true;
        }

        let optional_allocator_generic_type = if any_parameters_need_allocator_type {
            Some(quote!{ <A: std::alloc::Allocator> })
        } else { None };
        let (self_type_declaration, self_type_value_as_ptr) = if virtual_function_prototype.virtual_function.is_const_member_function {
            (quote!{ &self }, quote!{ self as *const Self as *mut u8 })
        } else { (quote!{ &mut self }, quote!{ self as *mut Self as *mut u8 }) };

        let source_function_name = &virtual_function_prototype.virtual_function.name;
        let return_value_declaration = return_value_tokens.return_value_type.map(|return_value_type| quote! { -> #return_value_type } );
        let before_return_value_statement = return_value_tokens.before_return_value_statement;
        let return_value_storage_initializer = return_value_tokens.return_value_storage_initializer.unwrap_or_else(|| quote! { std::ptr::null_mut() });
        let return_value_statement = return_value_tokens.return_expression;
        let return_value_through_storage = return_value_tokens.return_value_through_storage;

        let return_value_type_index_expression = return_value_tokens.return_value_static_type_tag.map(|rv_static_type_tag|
            quote! { Some(#rv_static_type_tag::store_type_descriptor_to_universe::<#type_universe>()) }).unwrap_or_else(|| quote! { None });

        let call_descriptor_parameter_typecheck = if has_any_dynamic_parameters {
            if virtual_function_prototype.variable_argument_count {
                // For variable argument count we have to allocate a dynamically sized parameter type vector
                let num_known_parameter_types = parameter_type_indices.len();
                quote! {
                    let dynamic_parameter_types: Vec<usize> = Vec::with_capacity(#num_known_parameter_types + extra_params.len());
                    dynamic_parameter_types.extend_from_slice([#(#parameter_type_indices),*]);
                    for dynamic_parameter in &extra_params {
                        dynamic_parameter_types.push(dynamic_parameter.type_index());
                    }
                    call_descriptor.validate_parameter_types(#source_function_name, return_value_type_index_expression, dynamic_parameter_types.into_iter());
                }
            } else {
                quote! { call_descriptor.validate_parameter_types(#source_function_name, #return_value_type_index_expression, [#(#parameter_type_indices),*].into_iter()); }
            }
        } else {
            quote! {
                if !call_descriptor.has_validated_parameter_types() {
                    call_descriptor.validate_parameter_types(#source_function_name, #return_value_type_index_expression, [#(#parameter_type_indices),*].into_iter());
                    call_descriptor.mark_parameter_types_validated();
                }
            }
        };

        let call_descriptor_invoke_call = if virtual_function_prototype.variable_argument_count {
            // For variable argument count we have to allocate a dynamically sized argument values container
            let num_known_parameters = parameter_ptr_values.len();
            quote! {
                    let dynamic_parameter_values: Vec<*mut u8> = Vec::with_capacity(#num_known_parameters + extra_params.len());
                    dynamic_parameter_values.extend_from_slice([#(#parameter_ptr_values),*]);
                    for dynamic_parameter in &extra_params {
                        dynamic_parameter_values.push(dynamic_parameter.as_raw_ptr());
                    }
                    (call_descriptor.get_call_thunk())(#self_type_value_as_ptr, return_value_storage, dynamic_parameter_values.as_ptr())
                }
        } else { quote!{ (call_descriptor.get_call_thunk())(#self_type_value_as_ptr, return_value_storage, [#(#parameter_ptr_values),*].as_ptr()) } };

        let check_function_available_fragment = if is_prototype_virtual_function {
            let check_existence_function_name = &Ident::new(&format!("check_available_{}", &function_name_string_sneak_case), Span::call_site());
            Some(quote! {
                pub fn #check_existence_function_name() {
                    use generic_statics::{define_namespace, Namespace};
                    define_namespace!(CheckExistenceType);
                    let check_function_exists = CheckExistenceType::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeCheckFunctionExists<Self, #type_universe>>();
                    check_function_exists.does_virtual_function_exist(#source_function_name)
                }
            })
        } else { None };

        let result_function_definition = quote! {
            #function_doc_comment
            pub fn #virtual_function_name #optional_allocator_generic_type (#self_type_declaration, #(#parameter_declarations),*) #return_value_declaration {
                use generic_statics::{define_namespace, Namespace};
                use gospel_runtime::core_type_definitions::StaticTypeTag;
                use gospel_runtime::local_type_model::ImplicitPtrMetadata;
                define_namespace!(CallDescriptor);
                let call_descriptor = CallDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeMethodCallDescriptor<Self, #type_universe>>();
                #call_descriptor_parameter_typecheck
                if !call_descriptor.has_prepared_call_thunk() {
                    call_descriptor.prepare_virtual_function_call_thunk(#source_function_name, #return_value_through_storage, &[#(#parameter_pass_by_reference),*]);
                }
                #before_return_value_statement
                let return_value_storage: *mut u8 = #return_value_storage_initializer;
                let return_value_direct: *mut u8 = unsafe { #call_descriptor_invoke_call };
                #return_value_statement
            }
            #check_function_available_fragment
        };
        Ok(result_function_definition)
    }
    fn generate_type_parameter_declaration(parameter_name: &Ident, parameter_type: &ExpressionValueType) -> anyhow::Result<(TokenStream, TokenStream)> {
        Ok(match parameter_type {
            // TODO: This should be BoolValueTypeTag but due to current implementation of VM value conversion for type references it cannot be
            ExpressionValueType::Bool => (quote! {
                #parameter_name : gospel_runtime::core_type_definitions::IntegralValueTypeTag + 'static
            }, quote! {
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Integer(_) => (quote! {
                #parameter_name : gospel_runtime::core_type_definitions::IntegralValueTypeTag + 'static
            }, quote!{
                gospel_typelib::type_model::TypeTemplateArgument::Integer(#parameter_name::get_raw_integral_value())
            }),
            ExpressionValueType::Typename => (quote!{
                #parameter_name : gospel_runtime::core_type_definitions::StaticTypeTag + ?Sized + 'static
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
            let (parameter_declaration, parameter_call_argument) = Self::generate_type_parameter_declaration(&parameter_name, &implicit_parameter.parameter_type)?;
            parameter_declarations.push(parameter_declaration);
            parameter_list.push(parameter_name);
            parameter_call_arguments.push(parameter_call_argument);
        }
        if let Some(explicit_parameters) = function_signature.explicit_parameters.as_ref() {
            for explicit_parameter in explicit_parameters {
                let parameter_name = Ident::new(explicit_parameter.parameter_declaration.upgrade().unwrap().name.as_str(), Span::call_site());
                let (parameter_declaration, parameter_call_argument) = Self::generate_type_parameter_declaration(&parameter_name, &explicit_parameter.parameter_type)?;
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
    fn collect_udt_field_prototypes(&self, type_container: &GospelVMTypeContainer, generated_field_names: &HashSet<String>) -> Vec<FieldPrototypeData> {
        let mut result_prototypes = type_container.member_prototypes.as_ref().unwrap().iter()
            .fold(HashMap::<String, HashSet<usize>>::new(), |mut field_type_map, member_prototype| {
                if let UserDefinedTypeMember::Field(field) = &member_prototype.member_declaration {
                    if let Some(field_name) = &field.name && !generated_field_names.contains(field_name) &&
                        field.member_type(&self.module_context.run_context) != &Type::Primitive(PrimitiveType::Void) {
                        field_type_map.entry(field_name.clone()).or_default().insert(field.member_type_index);
                    }
                }
                field_type_map
            })
            .into_iter()
            .map(|(field_name, field_type_indices)| FieldPrototypeData{field_name, field_type_index: field_type_indices.into_iter().next() })
            .collect::<Vec<FieldPrototypeData>>();
        result_prototypes.sort_by(|a, b| a.field_name.cmp(&b.field_name));
        result_prototypes
    }
    fn collect_udt_virtual_function_prototypes(&self, type_container: &GospelVMTypeContainer, generated_function_names: &HashSet<String>) -> Vec<VirtualFunctionPrototypeData> {
        let mut result_prototypes = type_container.member_prototypes.as_ref().unwrap().iter()
            .fold(HashMap::<String, VirtualFunctionPrototypeData>::new(), |mut virtual_function_map, member_prototype| {
                if let UserDefinedTypeMember::VirtualFunction(virtual_function) = &member_prototype.member_declaration &&
                    !virtual_function.is_virtual_function_override && !generated_function_names.contains(&virtual_function.name) {
                    if let Some(other_function_data) = virtual_function_map.get_mut(&virtual_function.name) {

                        // If our return type is unresolved, the entire prototype return type becomes unresolved
                        if member_prototype.unresolved_return_type {
                            other_function_data.virtual_function.return_value_type_index = virtual_function.return_value_type_index;
                            other_function_data.unresolved_return_type = true;
                        }

                        // If current prototype has more parameters than we do, trim the extra parameters and mark the argument count as variable
                        if other_function_data.virtual_function.parameters.len() > virtual_function.parameters.len() {
                            other_function_data.virtual_function.parameters.truncate(virtual_function.parameters.len());
                            other_function_data.variable_argument_count = true;
                        } else if other_function_data.virtual_function.parameters.len() < virtual_function.parameters.len() {
                            // If this function has more arguments than the prototype, mark the prototype argument count as variable
                            other_function_data.variable_argument_count = true;
                        }

                        // Reset const status of the function if the prototype is const but this function is not. Function is only const if all prototypes of it are const
                        if other_function_data.virtual_function.is_const_member_function && !virtual_function.is_const_member_function {
                            other_function_data.virtual_function.is_const_member_function = false;
                        }

                        // Walk the parameters and make sure they are consistent between the function and the prototype
                        for parameter_index in 0..other_function_data.virtual_function.parameters.len() {
                            let new_function_parameter = other_function_data.virtual_function.parameters[parameter_index].clone();
                            let current_function_parameter = &virtual_function.parameters[parameter_index];

                            if new_function_parameter.parameter_type_index != current_function_parameter.parameter_type_index {
                                // Parameter type is different between the prototype and the function, so parameter type is not known
                                other_function_data.unresolved_parameter_type_indices.insert(parameter_index);
                            } else if self.module_context.run_context.type_by_index(new_function_parameter.parameter_type_index) == &Type::Primitive(PrimitiveType::Void) {
                                // This parameter has type void, which is not valid and indicates a parameter with unresolved type, so mark it as such
                                other_function_data.unresolved_parameter_type_indices.insert(parameter_index);
                            }

                            if !other_function_data.nameless_parameter_indices.contains(&parameter_index) {
                                if new_function_parameter.parameter_name.is_none() && current_function_parameter.parameter_name.is_some() {
                                    // Function has the parameter name, but the prototype does not, so take the parameter name
                                    other_function_data.virtual_function.parameters[parameter_index].parameter_name = current_function_parameter.parameter_name.clone();
                                } else if new_function_parameter.parameter_name.is_some() && current_function_parameter.parameter_name.is_some() {
                                    if new_function_parameter.parameter_name != current_function_parameter.parameter_name {
                                        // Function and prototype both have parameter names that are different, as such this parameter becomes unnamed
                                        other_function_data.nameless_parameter_indices.insert(parameter_index);
                                        other_function_data.virtual_function.parameters[parameter_index].parameter_name = None;
                                    }
                                }
                            }
                        }
                    } else {
                        virtual_function_map.insert(virtual_function.name.clone(), VirtualFunctionPrototypeData{
                            virtual_function: virtual_function.clone(),
                            unresolved_return_type: member_prototype.unresolved_return_type,
                            ..VirtualFunctionPrototypeData::default()
                        });
                    }
                }
                virtual_function_map
            })
            .into_iter()
            .map(|(_, function_data)| function_data)
            .collect::<Vec<VirtualFunctionPrototypeData>>();

        result_prototypes.sort_by(|a, b| a.virtual_function.name.cmp(&b.virtual_function.name));
        result_prototypes
    }
    fn generate_udt_definition(&self, user_defined_type: &UserDefinedType, type_container: &GospelVMTypeContainer, type_definition: &BindingsTypeDefinition) -> anyhow::Result<TokenStream> {
        let full_type_name = user_defined_type.name.clone().unwrap();
        let type_doc_comment = Self::generate_doc_comment(type_definition, "doc");

        let mut generated_field_names: HashSet<String> = HashSet::new();
        let mut generated_fields: Vec<TokenStream> = Vec::new();

        // Generate exact fields definitions first
        for udt_member in &user_defined_type.members {
            if let UserDefinedTypeMember::Field(field) = udt_member && let Some(field_name) = field.name.as_ref() && !field_name.contains("@") {
                let field_tokens = self.generate_type_field_definition(field_name, &Ident::new(&Self::convert_field_name_to_snake_case(field_name), Span::call_site()),
                    Some(field.member_type_index), false, type_definition)?;
                generated_fields.push(field_tokens);
                generated_field_names.insert(field_name.clone());
            }
        }

        // Generate field prototypes for the rest of the fields
        let field_prototypes = self.collect_udt_field_prototypes(type_container, &generated_field_names);
        for field_prototype in &field_prototypes {
            let field_tokens = self.generate_type_field_definition(&field_prototype.field_name,
                &Ident::new(&Self::convert_field_name_to_snake_case(&field_prototype.field_name), Span::call_site()),
                field_prototype.field_type_index, true, type_definition)?;
            generated_fields.push(field_tokens);
        }

        let mut generated_virtual_function_names: HashSet<String> = HashSet::new();
        let mut generated_virtual_functions: Vec<TokenStream> = Vec::new();

        // Generate exact virtual functions first
        for udt_member in &user_defined_type.members {
            if let UserDefinedTypeMember::VirtualFunction(virtual_function) = udt_member && !virtual_function.is_virtual_function_override && !virtual_function.name.contains("@") {
                let function_prototype_data = VirtualFunctionPrototypeData{virtual_function: virtual_function.clone(), ..VirtualFunctionPrototypeData::default()};
                let virtual_function_tokens = self.generate_type_virtual_function_definition(&function_prototype_data, false, type_definition)?;
                generated_virtual_functions.push(virtual_function_tokens);
                generated_virtual_function_names.insert(function_prototype_data.virtual_function.name.clone());
            }
        }

        // Generate virtual function prototypes now
        let virtual_function_prototypes = self.collect_udt_virtual_function_prototypes(type_container, &generated_virtual_function_names);
        for virtual_function_prototype in &virtual_function_prototypes {
            if !virtual_function_prototype.virtual_function.name.contains("@") {
                let virtual_function_tokens = self.generate_type_virtual_function_definition(&virtual_function_prototype, true, type_definition)?;
                generated_virtual_functions.push(virtual_function_tokens);
            }
        }

        let type_name = Ident::new(&Self::generate_short_type_name(&full_type_name), Span::call_site());
        let function_signature = type_definition.function_declaration.as_ref().unwrap().reference.signature.clone();
        let TypeParameterTokens{ parameter_declaration, parameter_list, phantom_data_list, static_type_implementation } =
            self.generate_type_parameters_from_function_signature(&type_name, &full_type_name, &function_signature)?;

        let mut all_type_implementations: Vec<TokenStream> = Vec::new();
        all_type_implementations.push(static_type_implementation);

        if self.bindings_type == ModuleBindingsType::Local {
            let type_universe = self.generate_type_universe_full_name();
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
            if is_trivially_copyable(type_definition.function_declaration.as_ref().unwrap()) {
                all_type_implementations.push(quote! {
                    unsafe impl #parameter_declaration std::clone::CloneToUninit for #type_name #parameter_list {
                        unsafe fn clone_to_uninit(&self, dest: *mut u8) {
                            use gospel_runtime::local_type_model::ImplicitPtrMetadata;
                            dest.copy_from(self._private_bytes.as_ptr(), Self::static_size_of_val());
                        }
                    }
                });
            }
            if is_trivially_constructible(type_definition.function_declaration.as_ref().unwrap()) {
                all_type_implementations.push(quote! {
                    unsafe impl #parameter_declaration gospel_runtime::local_type_model::DefaultConstructAtUninit for #type_name #parameter_list {
                        unsafe fn default_construct_at(dest: *mut u8) {
                            use gospel_runtime::local_type_model::ImplicitPtrMetadata;
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
                #(#generated_virtual_functions)*
            }
        })
    }
    fn generate_enum_constant_definition(&self, enum_definition: &BindingsTypeDefinition, enum_underlying_type: &Option<PrimitiveType>, source_constant_name: &str, constant_name: Ident, is_prototype_constant: bool) -> TokenStream {
        let field_doc_comment = Self::generate_doc_comment(enum_definition, &format!("{}$doc", source_constant_name));
        match self.bindings_type {
            ModuleBindingsType::External => {
                if is_prototype_constant {
                    quote! { gsb_codegen_implement_external_enum_constant!(#constant_name, #source_constant_name, optional, { #field_doc_comment }); }
                } else {
                    quote! { gsb_codegen_implement_external_enum_constant!(#constant_name, #source_constant_name, required, { #field_doc_comment }); }
                }
            }
            ModuleBindingsType::Local => {
                let type_universe = self.generate_type_universe_full_name();
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
                        pub fn boxed_from_raw_discriminant<A : std::alloc::Allocator>(raw_discriminant: u64, alloc: A) -> Box<Self, A> { Box::<Self, A>::new_in(Self::sized_from_raw_discriminant(raw_discriminant), alloc) }
                    }
                });
                type_additional_attributes = Some(quote! {
                    #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
                    #[repr(transparent)]
                });
            } else {
                // Underlying type is unknown, so we have to generate the enum as a dynamically sized type
                let type_universe = self.generate_type_universe_full_name();
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
                            use gospel_runtime::local_type_model::ImplicitPtrMetadata;
                            dest.copy_from(self._private_bytes.as_ptr(), Self::static_size_of_val());
                        }
                    }
                    unsafe impl #parameter_declaration gospel_runtime::local_type_model::DefaultConstructAtUninit for #type_name #parameter_list {
                        unsafe fn default_construct_at(dest: *mut u8) {
                            use gospel_runtime::local_type_model::ImplicitPtrMetadata;
                            dest.write_bytes(0, Self::static_size_of_val());
                        }
                    }
                    impl #parameter_declaration #type_name #parameter_list {
                        pub fn boxed_to_raw_discriminant(&self) -> u64 {
                            use generic_statics::{define_namespace, Namespace};
                            define_namespace!(EnumTypeDescriptor);
                            EnumTypeDescriptor::generic_static::<gospel_runtime::local_type_model::CachedThreadSafeTypeSizeAndAlignment<Self, #type_universe>>().read_boxed_enum_value(self)
                        }
                        pub fn boxed_from_raw_discriminant<A : std::alloc::Allocator>(raw_discriminant: u64, alloc: A) -> Box<Self, A> {
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
        let parsed_file = parse_str::<File>(&result_file_token_stream.clone().to_string()).map_err(|x| {
            let contents_dump_location = absolute(temp_dir().join(PathBuf::from(format!("bindings_source_text_{}.rs", Uuid::new_v4())))).unwrap();
            write(&contents_dump_location, result_file_token_stream.to_string()).unwrap();
            anyhow!("Failed to parse generated file ({}:{}): {} (contents dumped to {})", x.span().start().line, x.span().start().column, x, contents_dump_location.display())
        })?;
        Ok(prettyplease::unparse(&parsed_file))
    }
}
