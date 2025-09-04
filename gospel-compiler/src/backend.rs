use std::cell::{Ref, RefCell, RefMut};
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;
use std::rc::{Rc, Weak};
use std::str::FromStr;
use anyhow::anyhow;
use itertools::{Itertools};
use strum::Display;
use crate::ast::{BoolConstantExpression, CVQualifiedExpression, CompilerBuiltinExpression, EnumConstantDeclaration, EnumStatement, FunctionParameterDeclaration, MemberFunctionDeclaration, StaticCastExpression};
use gospel_typelib::type_model::{BitWidth, EnumKind, IntegerSignedness, IntegralType, PrimitiveType, UserDefinedTypeKind};
use gospel_vm::bytecode::GospelOpcode;
use gospel_vm::module::GospelContainer;
use gospel_vm::gospel::{GospelTargetProperty};
use gospel_vm::writer::{GospelContainerBuilder, GospelContainerWriter, GospelJumpLabelFixup, GospelModuleVisitor, GospelSourceFunctionDefinition, GospelSourceObjectReference};
use crate::ast::{ASTSourceContext, AssignmentStatement, BlockStatement, ConditionalStatement, DataStatement, Expression, ExpressionValueType, InputStatement, DeclarationStatement, ImportStatement, ModuleImportStatementType, ModuleSourceFile, TopLevelDeclaration, NamespaceStatement, PartialIdentifier, PartialIdentifierKind, Statement, StructStatement, TemplateArgument, TemplateDeclaration, WhileLoopStatement, BinaryOperator, SimpleStatement, IdentifierExpression, UnaryExpression, UnaryOperator, BinaryExpression, ConditionalExpression, BlockExpression, IntegerConstantExpression, ArrayTypeExpression, MemberAccessExpression, StructInnerDeclaration, BlockDeclaration, ConditionalDeclaration, MemberDeclaration, DeclarationAccessSpecifier, PrimitiveTypeExpression, ExpressionWithCondition};
use crate::parser::parse_source_file;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompilerSourceContext {
    pub file_name: Option<String>,
    pub line_context: ASTSourceContext,
}
impl Display for CompilerSourceContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file_name.as_ref().map(String::as_str).unwrap_or("<unknown>"), self.line_context)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompilerError {
    pub source_context: CompilerSourceContext,
    pub description: String,
    pub chained_errors: Vec<CompilerError>,
}
impl Display for CompilerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.source_context, self.description)?;
        for chained_error in &self.chained_errors {
            writeln!(f, " -> {}", chained_error)?;
        }
        Ok({})
    }
}
macro_rules! compiler_error {
    ($context:expr, $fmt:expr, $($arg:tt)*) => {
        CompilerError{source_context: $context.clone(), description: format!($fmt, $($arg)*), chained_errors: Vec::new()}
    };
     ($context:expr, $message:expr) => {
        CompilerError{source_context: $context.clone(), description: $message.to_string(), chained_errors: Vec::new()}
    };
}

trait WithSourceContext<T> {
    fn with_source_context(self, source_context: &CompilerSourceContext) -> T;
}
impl<T, S, E : WithSourceContext<S>> WithSourceContext<Result<T, S>> for Result<T, E> {
    fn with_source_context(self, source_context: &CompilerSourceContext) -> Result<T, S> {
        self.map_err(|x| x.with_source_context(source_context))
    }
}
impl WithSourceContext<CompilerError> for anyhow::Error {
    fn with_source_context(self, source_context: &CompilerSourceContext) -> CompilerError {
        compiler_error!(source_context, self.to_string())
    }
}

type CompilerResult<T> = Result<T, CompilerError>;
macro_rules! compiler_bail {
    ($context:expr, $fmt:expr, $($arg:tt)*) => {
        return CompilerResult::Err(compiler_error!($context, $fmt, $($arg)*));
    };
     ($context:expr, $message:expr) => {
         return CompilerResult::Err(compiler_error!($context, $message));
    };
}

pub trait CompilerResultTrait<T> {
    fn to_simple_result(self) -> anyhow::Result<T>;
}
impl<T> CompilerResultTrait<T> for CompilerResult<T> {
    fn to_simple_result(self) -> anyhow::Result<T> {
        match self {
            Ok(value) => Ok(value),
            Err(compiler_error) => Err(anyhow!("{}", compiler_error))
        }
    }
}

trait ToCompositeCompilerResult<T> {
    fn collect_compiler_result<S: Fn() -> CompilerError>(self, composite_error: S) -> CompilerResult<Vec<T>>;
    fn chain_compiler_result<S: Fn() -> CompilerError>(self, composite_error: S) -> CompilerResult<()>;
}
impl<T, R> ToCompositeCompilerResult<T> for R where R: Iterator<Item = CompilerResult<T>> {
    fn collect_compiler_result<S: Fn() -> CompilerError>(self, composite_error: S) -> CompilerResult<Vec<T>> {
        let mut result_elements: Vec<T> = Vec::new();
        let mut result_errors: Vec<CompilerError> = Vec::new();

        self.for_each(|x| {
            match x {
                Ok(value) => { result_elements.push(value); }
                Err(error) => { result_errors.push(error); }
            };
        });
        if !result_errors.is_empty() {
            let mut base_compile_error = composite_error();
            base_compile_error.chained_errors.append(&mut result_errors);
            Err(base_compile_error)
        } else { Ok(result_elements) }
    }
    fn chain_compiler_result<S: Fn() -> CompilerError>(self, composite_error: S) -> CompilerResult<()> {
        let mut result_errors: Vec<CompilerError> = Vec::new();
        self.for_each(|x| {
            if let Err(error) = x {
                result_errors.push(error);
            };
        });
        if !result_errors.is_empty() {
            let mut base_compile_error = composite_error();
            base_compile_error.chained_errors.append(&mut result_errors);
            Err(base_compile_error)
        } else { Ok({}) }
    }
}

/// Represents an explicit function parameter declaration
#[derive(Debug, Clone)]
pub struct CompilerFunctionParameter {
    pub parameter_type: ExpressionValueType,
    pub default_value: Option<CompilerFunctionReference>,
    pub parameter_declaration: Weak<CompilerLexicalDeclaration>,
}

/// Represents a signature of the function with all the implicit and explicit parameters, as well as return value, listed
#[derive(Debug, Clone, Default)]
pub struct CompilerFunctionSignature {
    pub implicit_parameters: Vec<Weak<CompilerLexicalDeclaration>>,
    pub explicit_parameters: Option<Vec<CompilerFunctionParameter>>,
    pub return_value_type: ExpressionValueType,
}

/// Represents a reference to a function that can be used to call the function later
#[derive(Debug, Clone, Default)]
pub struct CompilerFunctionReference {
    pub function: GospelSourceObjectReference,
    pub signature: CompilerFunctionSignature,
    pub return_value_type_name: Option<String>,
}

/// Compiler options that affect the compilation of the source files and modules
#[derive(Debug, Clone)]
pub struct CompilerOptions {
    allow_partial_types: bool,
    generate_prototype_layouts: bool,
    implicit_narrowing_conversions: bool,
}
impl Default for CompilerOptions {
    fn default() -> Self {
        Self{allow_partial_types: false, generate_prototype_layouts: false, implicit_narrowing_conversions: false}
    }
}
impl CompilerOptions {
    /// Allows generation of partial UDT type definitions when members of the structs cannot be resolved
    pub fn allow_partial_types(mut self) -> Self {
        self.allow_partial_types = true; self
    }
    /// Generates additional metadata about the prototype layout of UDT types that can be useful to some users
    pub fn generate_prototype_layouts(mut self) -> Self {
        self.generate_prototype_layouts = true; self
    }
    /// Whenever implicit integer narrowing conversions are allowed
    pub fn allow_implicit_narrowing_conversions(mut self) -> Self {
        self.implicit_narrowing_conversions = true; self
    }
}

#[derive(Debug)]
pub struct CompilerInstance {
    compiler_options: CompilerOptions,
    module_scopes: RefCell<HashMap<String, Rc<CompilerLexicalScope>>>,
}

#[derive(Debug)]
struct CompilerFunctionBuilder {
    function_scope: Rc<CompilerLexicalScope>,
    function_signature: CompilerFunctionSignature,
    return_value_struct_name: Option<String>,
    function_name: GospelSourceObjectReference,
    function_definition: GospelSourceFunctionDefinition,
    argument_source_declarations: Vec<Rc<CompilerLexicalDeclaration>>,
    inline_struct_counter: usize,
}

impl CompilerFunctionBuilder {
    fn pre_compile_function(function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<(GospelSourceObjectReference, CompilerFunctionSignature, Option<String>, Vec<Rc<CompilerLexicalDeclaration>>)> {
        let function_reference = if let CompilerLexicalScopeClass::Function(function_closure) = &function_scope.class {
            let borrowed_closure = function_closure.borrow();
            borrowed_closure.reference.clone()
        } else {
            compiler_bail!(&function_scope.source_context, "Internal compiler error: expected data scope in CompilerFunctionBuilder");
        };
        let mut argument_source_declarations: Vec<Rc<CompilerLexicalDeclaration>> = Vec::new();

        for weak_implicit_parameter in &function_reference.signature.implicit_parameters {
            if let Some(implicit_parameter) = weak_implicit_parameter.upgrade() {
                match &implicit_parameter.class {
                    CompilerLexicalDeclarationClass::Parameter(_) => {
                        argument_source_declarations.push(implicit_parameter);
                    }
                    CompilerLexicalDeclarationClass::LocalVariable(_) => {
                        argument_source_declarations.push(implicit_parameter);
                    }
                    _ => { compiler_bail!(&function_scope.source_context, "Internal compiler error: expected Parameter or LocalVariable declaration as implicit function parameters, got {}", implicit_parameter.class); }
                }
            } else {
                compiler_bail!(&function_scope.source_context, "Internal compiler error: lost reference to the implicit function parameter");
            }
        }

        if let Some(explicit_function_parameters) = &function_reference.signature.explicit_parameters {
            for explicit_function_parameter in explicit_function_parameters {
                if let Some(parameter_declaration) = explicit_function_parameter.parameter_declaration.upgrade() {
                    argument_source_declarations.push(parameter_declaration);
                } else {
                    compiler_bail!(&function_scope.source_context, "Internal compiler error: lost reference to the explicit function parameter");
                }
            }
        }
        Ok((function_reference.function.clone(), function_reference.signature, function_reference.return_value_type_name.clone(), argument_source_declarations))
    }
    fn create(function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<CompilerFunctionBuilder> {
        let (function_name, function_signature, return_value_struct_name, argument_source_declarations) = Self::pre_compile_function(function_scope)?;
        Ok(CompilerFunctionBuilder{
            function_scope: function_scope.clone(),
            function_signature: function_signature.clone(),
            return_value_struct_name,
            function_name,
            function_definition: GospelSourceFunctionDefinition::create(function_scope.visibility == DeclarationVisibility::Public, function_scope.source_context.file_name.clone().unwrap_or(String::from("<builtin>"))),
            argument_source_declarations,
            inline_struct_counter: 0,
        })
    }
    fn compile_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &Expression) -> CompilerResult<ExpressionValueType> {
        match expression {
            Expression::IdentifierExpression(identifier_expression) => { self.compile_identifier_expression(scope, &*identifier_expression) }
            Expression::UnaryExpression(unary_expression) => { self.compile_unary_expression(scope, &*unary_expression) }
            Expression::BinaryExpression(binary_expression) => { self.compile_binary_expression(scope, &*binary_expression) }
            Expression::ConditionalExpression(conditional_expression) => { self.compile_conditional_expression(scope, &*conditional_expression) }
            Expression::BlockExpression(block_expression) => { self.compile_block_expression(scope, &*block_expression) }
            Expression::IntegerConstantExpression(constant_expression) => { self.compile_integer_constant_expression(scope, &*constant_expression) }
            Expression::BoolConstantExpression(constant_expression) => { self.compile_bool_constant_expression(scope, &**constant_expression) }
            Expression::ArrayIndexExpression(array_index_expression) => { self.compile_array_type_expression(scope, &*array_index_expression) }
            Expression::MemberAccessExpression(member_access_expression) => { self.compile_member_access_expression(scope, &*member_access_expression) }
            Expression::StructDeclarationExpression(struct_declaration_expression) => { self.compile_struct_declaration_expression(scope, &*struct_declaration_expression) }
            Expression::CompilerBuiltinExpression(compiler_builtin_expression) => { self.compile_compiler_builtin_expression(scope, &*compiler_builtin_expression) }
            Expression::PrimitiveTypeExpression(primitive_type_expression) => { self.compile_primitive_type_expression(scope, &*primitive_type_expression) }
            Expression::CVQualifiedExpression(cv_qualified_expression) => { self.compile_cv_qualified_expression(scope, &*cv_qualified_expression) }
            Expression::StaticCastExpression(static_cast_expression) => { self.compile_static_cast_expression(scope, &*static_cast_expression) }
        }
    }
    fn compile_compiler_builtin_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &CompilerBuiltinExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        if let Ok(target_property) = GospelTargetProperty::from_str(&expression.identifier) {
            self.function_definition.add_string_instruction(GospelOpcode::LoadTargetProperty, &target_property.to_string(), Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok(ExpressionValueType::Integer(IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}))
        } else {
            Err(compiler_error!(&source_context, "Unknown compiler builtin: {}", &expression.identifier))
        }
    }
    fn compile_primitive_type_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &PrimitiveTypeExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        self.function_definition.add_string_instruction(GospelOpcode::TypePrimitiveCreate, &expression.primitive_type.to_string(), Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok(ExpressionValueType::Typename)
    }
    fn compile_cv_qualified_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &CVQualifiedExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let base_expression_type = self.compile_expression(scope, &expression.base_expression)?;
        self.coerce_to_expression_type(&base_expression_type, &ExpressionValueType::Typename, &source_context)?;
        if expression.constant {
            self.function_definition.add_simple_instruction(GospelOpcode::TypeAddConstantQualifier, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        }
        if expression.volatile {
            self.function_definition.add_simple_instruction(GospelOpcode::TypeAddVolatileQualifier, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        }
        Ok(ExpressionValueType::Typename)
    }
    fn compile_static_cast_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &StaticCastExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let cast_expression_type = self.compile_expression(scope, &expression.cast_expression)?;
        if let ExpressionValueType::Integer(target_integral_value_type) = &expression.target_type {
            // Casting to an integral type can be done from a bool or another integral type
            self.coerce_to_integral_type(target_integral_value_type, &cast_expression_type, true, &source_context)
        } else if let ExpressionValueType::Bool = &expression.target_type {
            // Casting to bool type can be done from any other type that can be normally coerced to bool in other contexts
            self.coerce_to_bool_type(&cast_expression_type, &source_context)
        } else {
            // Cannot cast to non-primitive types
            Err(compiler_error!(&source_context, "Cannot static cast to {}. Static cast can only be used to cast to integral types and bool", &expression.target_type))
        }
    }
    fn compile_struct_declaration_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &StructStatement) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let struct_function_name = format!("@inline_struct@{}", self.inline_struct_counter);
        self.inline_struct_counter += 1;
        let struct_reference = CompilerInstance::compile_struct_statement(scope, expression, Some(struct_function_name.as_str()), DeclarationVisibility::Private)?;
        self.compile_static_function_call(scope, &struct_reference, &source_context, None, true)
    }
    fn compile_member_access_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &MemberAccessExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        let target_expression_type = self.compile_expression(scope, &expression.type_expression)?;
        self.coerce_to_expression_type(&target_expression_type, &ExpressionValueType::Typename, &source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::TypeUDTGetMetadata, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        if let Some(template_arguments) = &expression.template_arguments {
            // Member access expression is a closure call, so we need to read the value as the closure and then call it
            self.function_definition.add_string_instruction(GospelOpcode::StructGetField, expression.member_name.as_str(), Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            for function_argument_expression in template_arguments {
                self.compile_expression(scope, function_argument_expression)?;
            }
            self.function_definition.add_variadic_instruction(GospelOpcode::Call, template_arguments.len() as u32, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok(expression.member_type.clone())
        } else {
            // Member access expression is just a read from the metadata struct, not a closure call. StructGetNamedTypedField will do a runtime typecheck for us
            self.function_definition.add_string_instruction(GospelOpcode::StructGetField, expression.member_name.as_str(), Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok(expression.member_type.clone())
        }
    }
    fn coerce_to_integral_type(&mut self, desired_type: &IntegralType, actual_type: &ExpressionValueType, allow_narrowing_conversion: bool, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        let from_instruction_encoding = Self::check_integral_or_bool_type_instruction_encoding(actual_type, source_context)?;
        let to_instruction_encoding = Self::integral_type_instruction_encoding(&desired_type);

        // Disallow implicit narrowing conversions between integral types. Note that implicit conversion to bool is okay in this case (at least for now)
        let disallow_narrowing = !allow_narrowing_conversion && !self.function_scope.compiler().map(|x| x.compiler_options.implicit_narrowing_conversions).unwrap_or(false);
        if disallow_narrowing && let ExpressionValueType::Integer(actual_integral_type) = actual_type && actual_integral_type.bit_width > desired_type.bit_width {
            compiler_bail!(source_context, "Implicit narrowing conversion from {} to {} is not allowed. Consider using static_cast if narrowing conversion is desired", actual_type, ExpressionValueType::Integer(desired_type.clone()));
        }
        let combined_instruction_encoding = (to_instruction_encoding << 16) | from_instruction_encoding;
        self.function_definition.add_int_instruction(GospelOpcode::IntCast, combined_instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
        Ok(ExpressionValueType::Integer(desired_type.clone()))
    }
    fn integral_type_instruction_encoding(value_type: &IntegralType) -> u32 {
        let bit_width_encoding: u32 = match value_type.bit_width {
            BitWidth::Width8 => 0x00,
            BitWidth::Width16 => 0x01,
            BitWidth::Width32 => 0x02,
            BitWidth::Width64 => 0x03,
        };
        let signedness_encoding: u32 = match value_type.signedness {
            IntegerSignedness::Signed => 0x80,
            IntegerSignedness::Unsigned => 0x0,
        };
        bit_width_encoding | signedness_encoding
    }
    fn coerce_to_bool_type(&mut self, actual_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        match actual_type {
            ExpressionValueType::Bool => Ok(ExpressionValueType::Bool),
            ExpressionValueType::Integer(integral_value_type) => {
                let instruction_encoding = Self::integral_type_instruction_encoding(integral_value_type);
                // This is equivalent of !! in C and C++, by comparing to zero we get the inverse of bool value, and then by comparing it again we got the actual value
                self.function_definition.add_int_instruction(GospelOpcode::Eqz, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                let bool_instruction_encoding = Self::bool_type_instruction_encoding();
                self.function_definition.add_int_instruction(GospelOpcode::Eqz, bool_instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            },
            _ => Err(compiler_error!(source_context, "Expected bool or integral type, got {}", actual_type))
        }
    }
    fn bool_type_instruction_encoding() -> u32 {
        Self::integral_type_instruction_encoding(&IntegralType {bit_width: BitWidth::Width8, signedness: IntegerSignedness::Unsigned})
    }
    fn check_integral_or_bool_type_instruction_encoding(expression_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<u32> {
        match expression_type {
            ExpressionValueType::Bool => Ok(Self::bool_type_instruction_encoding()),
            ExpressionValueType::Integer(integral_value_type) => Ok(Self::integral_type_instruction_encoding(integral_value_type)),
            _ => Err(compiler_error!(source_context, "Expected integral type or bool, got {}", expression_type))
        }
    }
    fn check_integral_type(expression_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<IntegralType> {
        if let ExpressionValueType::Integer(x) = expression_type {
            Ok(x.clone())
        } else {
            Err(compiler_error!(source_context, "Expected integral type, got {}", source_context))
        }
    }
    fn coerce_to_expression_type(&mut self, actual_type: &ExpressionValueType, desired_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        if desired_type == actual_type {
            // Types of expressions match, nothing to be done here
            Ok(actual_type.clone())
        } else if let ExpressionValueType::Integer(desired_integral_value_type) = desired_type {
            // Attempt to convert expression value to the integral type
            self.coerce_to_integral_type(desired_integral_value_type, actual_type, false, source_context)
        } else if let ExpressionValueType::Bool = desired_type {
            // Attempt to convert expression value to bool
            self.coerce_to_bool_type(actual_type, source_context)
        } else {
            // Do not know how to convert to another types implicitly
            compiler_bail!(source_context, "Expression type mismatch: expected {}, got {}", desired_type, actual_type);
        }
    }
    fn compile_array_type_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &ArrayTypeExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        let element_expression_type = self.compile_expression(scope, &expression.element_type_expression)?;
        self.coerce_to_expression_type(&element_expression_type, &ExpressionValueType::Typename, &source_context)?;

        let length_expression_type = self.compile_expression(scope, &expression.array_length_expression)?;
        Self::coerce_to_integral_type(self, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &length_expression_type, false, &source_context)?;

        self.function_definition.add_simple_instruction(GospelOpcode::TypeArrayCreate, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok(ExpressionValueType::Typename)
    }
    fn compile_integer_constant_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &IntegerConstantExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        match expression.constant_type.bit_width {
            BitWidth::Width8 => {
                self.function_definition.add_int_instruction(GospelOpcode::Int8Constant, expression.raw_constant_value as u8 as u32, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            },
            BitWidth::Width16 => {
                self.function_definition.add_int_instruction(GospelOpcode::Int16Constant, expression.raw_constant_value as u16 as u32, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            },
            BitWidth::Width32 => {
                self.function_definition.add_int_instruction(GospelOpcode::Int32Constant, expression.raw_constant_value as u32, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            },
            BitWidth::Width64 => {
                self.function_definition.add_int64_constant_instruction(expression.raw_constant_value, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            }
        }
        Ok(ExpressionValueType::Integer(expression.constant_type.clone()))
    }
    fn compile_bool_constant_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BoolConstantExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let literal_value: u32 = if expression.bool_value { 1 } else { 0 };
        self.function_definition.add_int_instruction(GospelOpcode::Int8Constant, literal_value, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok(ExpressionValueType::Bool)
    }
    fn coerce_integer_constant_expression(expression: &IntegerConstantExpression, desired_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<u64> {
        if let ExpressionValueType::Integer(desired_integral_type) = desired_type {
            Ok(IntegralType::cast_integral_value(expression.raw_constant_value, &expression.constant_type, desired_integral_type))
        } else if let ExpressionValueType::Bool = desired_type {
            if expression.raw_constant_value == 0 { Ok(0u64) } else { Ok(1u64) }
        } else {
            Err(compiler_error!(source_context, "Expected integral type or bool, got {}", desired_type))
        }
    }
    fn compile_block_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BlockExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Compile all statements in the block and then push the return value expression on the stack
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let block_scope = scope.declare_scope_generated_name("block", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: block_declaration.clone()}), &source_context.line_context)?;
        let block_start_instruction_index = self.function_definition.current_instruction_count();
        for statement in &expression.statements {
            self.compile_statement(&block_scope, statement)?;
        }
        let return_value_expression_type = self.compile_expression(&block_scope, &expression.return_value_expression)?;
        block_declaration.borrow_mut().block_range = CompilerInstructionRange{
            start_instruction_index: block_start_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };
        Ok(return_value_expression_type)
    }
    fn compile_conditional_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &ConditionalExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Evaluate the condition, and jump to the else block if it is zero
        let condition_expression_type = self.compile_expression(scope, &expression.condition_expression)?;
        self.coerce_to_bool_type(&condition_expression_type, &source_context)?;
        let instruction_encoding = Self::bool_type_instruction_encoding();
        let (_, jump_to_else_block_fixup) = self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        // We did not jump to the else block, which means the condition was true. Evaluate the true branch and jump to the end
        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let then_branch_block = scope.declare_scope_generated_name("then", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: then_block_declaration.clone()}), &source_context.line_context)?;
        let then_instruction_index = self.function_definition.current_instruction_count();
        let then_expression_type = self.compile_expression(&then_branch_block, &expression.true_expression)?;

        let (_, jump_to_end_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        then_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
            start_instruction_index: then_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };

        let else_block_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_else_block_fixup, else_block_instruction_index).with_source_context(&source_context)?;

        // We jumped to the else block, evaluate the false branch
        let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let else_branch_block = scope.declare_scope_generated_name("else", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: else_block_declaration.clone()}), &source_context.line_context)?;
        let else_expression_type = self.compile_expression(&else_branch_block, &expression.false_expression)?;
        else_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
            start_instruction_index: else_block_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };

        let end_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&source_context)?;

        // Validate that two branches of the conditional result in the expression of the same type
        if then_expression_type != else_expression_type {
            compiler_bail!(source_context, "Expression type mismatch: got expression of type {} on the true branch of the conditional, and expression of type {} on the false branch", then_expression_type, else_expression_type);
        }
        Ok(then_expression_type)
    }
    fn coerce_binary_operator_to_common_type(&mut self, left_side_type: &ExpressionValueType, right_side_type: &ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        if left_side_type == right_side_type {
            // If types on the left and the right are identical, no coercion is necessary
            Ok(left_side_type.clone())
        } else if let ExpressionValueType::Integer(left_side_integral_type) = left_side_type && let ExpressionValueType::Bool = right_side_type {
            // Right side bool gets promoted to an integer
            self.coerce_to_integral_type(left_side_integral_type, right_side_type, false, source_context)?;
            Ok(left_side_type.clone())
        }  else if let ExpressionValueType::Bool = left_side_type && let ExpressionValueType::Integer(right_side_integral_type) = right_side_type {
            // Left side bool gets promoted to an integer
            self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
            self.coerce_to_integral_type(right_side_integral_type, left_side_type, false, source_context)?;
            self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
            Ok(right_side_type.clone())
        } else if let ExpressionValueType::Integer(left_side_integral_type) = left_side_type && let ExpressionValueType::Integer(right_side_integral_type) = right_side_type {
            // Either left side or right side get converted to an integral type with a larger bit width. If the bit width is the same, type on the left wins
            if left_side_integral_type.bit_width >= right_side_integral_type.bit_width {
                // Left side is of the bigger or the same bit width than the right side, so right side needs to be widened to the left side type
                self.coerce_to_integral_type(left_side_integral_type, &right_side_type, false, source_context)?;
                Ok(left_side_type.clone())
            } else {
                // Right side is of the bigger bit width than the left side, so left side needs to be widened to the right side type
                self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
                self.coerce_to_integral_type(right_side_integral_type, &left_side_type, false, source_context)?;
                self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(right_side_type.clone())
            }
        } else {
            compiler_bail!(source_context, "Expression type mismatch: got expression of type {} on the left side of binary operator, and expression of type {} on the right side", left_side_type, right_side_type);
        }
    }
    fn compile_binary_operator(&mut self, left_side_type_aaa: &ExpressionValueType, right_side_type: &ExpressionValueType, source_context: &CompilerSourceContext, operator: BinaryOperator) -> CompilerResult<ExpressionValueType> {
        let common_expression_type: ExpressionValueType = self.coerce_binary_operator_to_common_type(left_side_type_aaa, right_side_type, source_context)?;
        match operator {
            // Bitwise operators
            BinaryOperator::BitwiseOr => {
                let instruction_encoding = Self::check_integral_or_bool_type_instruction_encoding(&common_expression_type, source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::Or, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::BitwiseXor => {
                let instruction_encoding = Self::check_integral_or_bool_type_instruction_encoding(&common_expression_type, source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::Xor, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::BitwiseAnd => {
                let instruction_encoding = Self::check_integral_or_bool_type_instruction_encoding(&common_expression_type, source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::And, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::BitwiseShiftLeft => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Shl, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::BitwiseShiftRight => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Shr, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            // Arithmetic operators
            BinaryOperator::ArithmeticAdd => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Add, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::ArithmeticSubtract => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Sub, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::ArithmeticMultiply => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Mul, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::ArithmeticDivide => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Div, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            BinaryOperator::ArithmeticRemainder => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::Rem, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(common_expression_type)
            }
            // Logical operators
            BinaryOperator::LogicalLess => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                self.function_definition.add_int_instruction(GospelOpcode::CmpLess, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::LogicalMore => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                // left > right = right < left
                self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::CmpLess, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::LogicalLessEquals => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                // left <= right
                self.function_definition.add_int_instruction(GospelOpcode::CmpLeq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::LogicalMoreEquals => {
                let left_side_integral_type = Self::check_integral_type(&common_expression_type, source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&left_side_integral_type);
                // left >= right = right <= left
                self.function_definition.add_simple_instruction(GospelOpcode::Permute, Self::get_line_number(source_context)).with_source_context(source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::CmpLeq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::Equals => {
                // Use CmpEq for integer comparison, and TypeIsSameType for types
                if let ExpressionValueType::Integer(integral_type) = &common_expression_type {
                    let instruction_encoding = Self::integral_type_instruction_encoding(&integral_type);
                    self.function_definition.add_int_instruction(GospelOpcode::CmpEq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else if common_expression_type == ExpressionValueType::Bool {
                    let instruction_encoding = Self::bool_type_instruction_encoding();
                    self.function_definition.add_int_instruction(GospelOpcode::CmpEq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else if common_expression_type == ExpressionValueType::Typename {
                    self.function_definition.add_simple_instruction(GospelOpcode::TypeIsSameType, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else {
                    compiler_bail!(source_context, "Comparison is only allowed for integers and types");
                }
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::NotEquals => {
                // Use Ez for integer comparison, and TypeIsSameType for types
                if let ExpressionValueType::Integer(integral_type) = &common_expression_type {
                    let instruction_encoding = Self::integral_type_instruction_encoding(&integral_type);
                    self.function_definition.add_int_instruction(GospelOpcode::CmpEq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else if common_expression_type == ExpressionValueType::Bool {
                    let instruction_encoding = Self::bool_type_instruction_encoding();
                    self.function_definition.add_int_instruction(GospelOpcode::CmpEq, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else if common_expression_type == ExpressionValueType::Typename {
                    self.function_definition.add_simple_instruction(GospelOpcode::TypeIsSameType, Self::get_line_number(source_context)).with_source_context(source_context)?;
                } else {
                    compiler_bail!(source_context, "Comparison is only allowed for integers and types");
                }
                let result_instruction_encoding = Self::bool_type_instruction_encoding();
                self.function_definition.add_int_instruction(GospelOpcode::Eqz, result_instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            BinaryOperator::ShortCircuitAnd => {
                // Handling in compile_short_circuit_binary_operator
                Err(compiler_error!(source_context, "Short circuited operators not supported by compile_binary_operator"))
            }
            BinaryOperator::ShortCircuitOr => {
                // Handling in compile_short_circuit_binary_operator
                Err(compiler_error!(source_context, "Short circuited operators not supported by compile_binary_operator"))
            }
        }
    }
    fn compile_short_circuit_binary_operator(&mut self, scope: &Rc<CompilerLexicalScope>, source_context: &CompilerSourceContext, left_side: &Expression, right_side: &Expression, operator: BinaryOperator) -> CompilerResult<ExpressionValueType> {
        let left_expression_type = self.compile_expression(scope, &left_side)?;
        self.coerce_to_bool_type(&left_expression_type, &source_context)?;
        let instruction_encoding = Self::bool_type_instruction_encoding();

        // Duplicate the left side value
        self.function_definition.add_simple_instruction(GospelOpcode::Dup, Self::get_line_number(source_context)).with_source_context(source_context)?;
        if operator == BinaryOperator::ShortCircuitOr {
            // If the left side value is not zero, jump to the end of the operator (and return that value, which is non-zero in this case)
            self.function_definition.add_int_instruction(GospelOpcode::Eqz, instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;
        } else if operator == BinaryOperator::ShortCircuitAnd {
            // If the left side value is zero, jump to the end of the operator (and return that value, which is zero in this case)
        } else {
            compiler_bail!(source_context, "Only short circuited operators are supported by compile_short_circuit_binary_operator");
        }
        let (_, jump_to_end_fixup) = self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(source_context)).with_source_context(source_context)?;

        // We will end up here if the left side value is not zero. Now we can execute the right side and return its value
        // Make sure to drop the duplicated left side beforehand though. We duplicate the value to remove the need to generate the else branch (since Branchz consumes the value)
        self.function_definition.add_simple_instruction(GospelOpcode::Pop, Self::get_line_number(source_context)).with_source_context(source_context)?;
        let right_expression_type = self.compile_expression(scope, &right_side)?;
        self.coerce_to_bool_type(&right_expression_type, &source_context)?;

        let end_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&source_context)?;
        Ok(ExpressionValueType::Bool)
    }
    fn compile_binary_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BinaryExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Use shared routine for handling operators that do not short circuit and can have both expressions evaluated immediately
        if expression.operator != BinaryOperator::ShortCircuitAnd && expression.operator != BinaryOperator::ShortCircuitOr {
            let left_expression_type = self.compile_expression(scope, &expression.left_expression)?;
            let right_expression_type = self.compile_expression(scope, &expression.right_expression)?;

            self.compile_binary_operator(&left_expression_type, &right_expression_type, &source_context, expression.operator)
        } else {
            // Use separate routine to handle short circuit operators
            self.compile_short_circuit_binary_operator(scope, &source_context, &expression.left_expression, &expression.right_expression, expression.operator)
        }
    }
    fn compile_unary_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &UnaryExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let inner_expression_type = self.compile_expression(scope, &expression.expression)?;

        match expression.operator {
            UnaryOperator::StructAlignOf => {
                self.coerce_to_expression_type(&inner_expression_type, &ExpressionValueType::Typename, &source_context)?;
                self.function_definition.add_simple_instruction(GospelOpcode::TypeCalculateAlignment, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(ExpressionValueType::Integer(IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}))
            }
            UnaryOperator::StructSizeOf => {
                self.coerce_to_expression_type(&inner_expression_type, &ExpressionValueType::Typename, &source_context)?;
                self.function_definition.add_simple_instruction(GospelOpcode::TypeCalculateSize, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(ExpressionValueType::Integer(IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}))
            }
            UnaryOperator::CreatePointerType => {
                self.coerce_to_expression_type(&inner_expression_type, &ExpressionValueType::Typename, &source_context)?;
                self.function_definition.add_simple_instruction(GospelOpcode::TypePointerCreate, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(ExpressionValueType::Typename)
            }
            UnaryOperator::CreateReferenceType => {
                self.coerce_to_expression_type(&inner_expression_type, &ExpressionValueType::Typename, &source_context)?;
                self.function_definition.add_simple_instruction(GospelOpcode::TypePointerCreateReference, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(ExpressionValueType::Typename)
            }
            UnaryOperator::BoolNegate => {
                let instruction_encoding = Self::check_integral_or_bool_type_instruction_encoding(&inner_expression_type, &source_context)?;
                self.function_definition.add_int_instruction(GospelOpcode::Eqz, instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(ExpressionValueType::Bool)
            }
            UnaryOperator::BitwiseInverse => {
                let integral_value_type = Self::check_integral_type(&inner_expression_type, &source_context)?;
                let instruction_encoding = Self::integral_type_instruction_encoding(&integral_value_type);
                self.function_definition.add_int_instruction(GospelOpcode::ReverseBits, instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(inner_expression_type)
            }
            UnaryOperator::ArithmeticNegate => {
                let integral_value_type = Self::check_integral_type(&inner_expression_type, &source_context)?;
                if integral_value_type.signedness != IntegerSignedness::Signed {
                    compiler_bail!(source_context, "Negate unary operator can only be applied to signed integral types");
                }
                let instruction_encoding = Self::integral_type_instruction_encoding(&integral_value_type);
                self.function_definition.add_int_instruction(GospelOpcode::Neg, instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                Ok(inner_expression_type)
            }
        }
    }
    fn compile_argument_value(&mut self, source_context: &CompilerSourceContext, argument_declaration: &Rc<CompilerLexicalDeclaration>, argument_type: ExpressionValueType) -> CompilerResult<ExpressionValueType> {
        let argument_index = self.argument_source_declarations.iter()
            .enumerate()
            .find(|(_, parameter_declaration)| Rc::ptr_eq(*parameter_declaration, &argument_declaration))
            .map(|(parameter_index, _)| parameter_index)
            .ok_or_else(|| compiler_error!(source_context, "Could not find function argument for parameter {}", argument_declaration.name))?;

        self.function_definition.add_load_argument_value_instruction(argument_index as u32, Self::get_line_number(source_context)).with_source_context(source_context)?;
        Ok(argument_type)
    }
    fn compile_lexical_declaration_access(&mut self, source_context: &CompilerSourceContext, declaration: &Rc<CompilerLexicalDeclaration>) -> CompilerResult<ExpressionValueType> {
        match &declaration.class {
            CompilerLexicalDeclarationClass::LocalVariable(local_variable) => {
                // When compiling inline struct definitions, we can capture local variables from the current scope, which will be converted to implicit parameters
                // Such local variables do not belong to the current function, and should be looked up as parameters instead. So only treat local variable as actual local variable if it is declared within this functions scope
                if declaration.parent.upgrade().map(|x| x.is_child_of(&self.function_scope)).unwrap_or(false) {
                    self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, local_variable.value_slot, Self::get_line_number(source_context)).with_source_context(source_context)?;
                    Ok(local_variable.variable_type.clone())
                } else {
                    self.compile_argument_value(source_context, &declaration, local_variable.variable_type.clone())
                }
            }
            CompilerLexicalDeclarationClass::Parameter(parameter_type) => {
                self.compile_argument_value(source_context, &declaration, parameter_type.clone())
            }
            CompilerLexicalDeclarationClass::GlobalData(global_data) => {
                self.function_definition.add_string_instruction(GospelOpcode::LoadGlobalVariable, &global_data.global_name, Self::get_line_number(source_context)).with_source_context(source_context)?;
                Ok(global_data.value_type.clone())
            }
            _ => Err(compiler_error!(source_context, "Declaration {} does not name a local or global variable or template parameter", declaration.name))
        }
    }
    fn load_function_and_implicit_arguments(&mut self, scope: &Rc<CompilerLexicalScope>, function: &CompilerFunctionReference, source_context: &CompilerSourceContext) -> CompilerResult<usize> {
        // Load the function closure for the function in question
        self.function_definition.add_function_instruction(GospelOpcode::LoadFunctionClosure, function.function.clone(), Self::get_line_number(source_context)).with_source_context(source_context)?;

        // Implicit parameters precede any explicit parameters
        for weak_implicit_parameter in &function.signature.implicit_parameters {
            let implicit_parameter = weak_implicit_parameter.upgrade()
                .ok_or_else(|| compiler_error!(source_context, "Internal error, reference to function declaration scope lost"))?;
            let implicit_parameter_scope = implicit_parameter.parent.upgrade()
                .ok_or_else(|| compiler_error!(source_context, "Internal error, reference to function declaration parent scope lost"))?;

            // Make sure the implicit parameter is actually available in the current scope. Implicit lexical parameters are only available in child scopes and only if their visibility context allows it
            if !self.function_scope.is_child_of(&implicit_parameter_scope) || !implicit_parameter_scope.is_declaration_visible(implicit_parameter.visibility, &self.function_scope.visibility_context()) {
                compiler_bail!(source_context, "Cannot access {} because it's implicit parameter {} from scope {} is not available in the current scope ({})",
                    function.function, implicit_parameter.name.as_str(), implicit_parameter_scope.full_scope_display_name(), scope.full_scope_display_name());
            }
            self.compile_lexical_declaration_access(source_context, &implicit_parameter)?;
        }
        Ok(function.signature.implicit_parameters.len())
    }
    fn compile_static_function_call(&mut self, scope: &Rc<CompilerLexicalScope>, function: &CompilerFunctionReference, source_context: &CompilerSourceContext, explicit_arguments: Option<&Vec<Expression>>, is_synthetic_function_call: bool) -> CompilerResult<ExpressionValueType> {
        // Load the function and the implicit arguments on the stack
        let implicit_parameter_count = self.load_function_and_implicit_arguments(scope, function, source_context)?;

        // Follow up explicit parameters with implicit parameters
        if function.signature.explicit_parameters.is_some() && explicit_arguments.is_some() {
            let parameter_types = function.signature.explicit_parameters.as_ref().unwrap();
            let parameter_expressions = explicit_arguments.as_ref().unwrap();

            if parameter_types.len() < parameter_expressions.len() && !is_synthetic_function_call {
                compiler_bail!(source_context, "Template argument number mismatch: expected at most {} arguments, but {} arguments were provided", parameter_types.len(), parameter_expressions.len());
            }
            let mut currently_provided_parameter_expressions: Vec<Expression> = Vec::new();
            for parameter_index in 0..parameter_types.len() {
                if parameter_index < parameter_expressions.len() {
                    // This function parameter has been provided by the user, so push its value on the stack
                    let provided_parameter_type = self.compile_expression(scope, &parameter_expressions[parameter_index])?;
                    self.coerce_to_expression_type(&provided_parameter_type, &parameter_types[parameter_index].parameter_type, &source_context)?;
                    // Cache the parameter value expression in case we need it as an input for evaluation of the default argument value down the line
                    currently_provided_parameter_expressions.push(parameter_expressions[parameter_index].clone());
                } else if let Some(default_parameter_value_provider) = &parameter_types[parameter_index].default_value {
                    // This function has a default parameter value, so compile the call to the function producing it
                    // Such a function can receive implicit parameters from the parent scope, as well as the values of the parameters before this one
                    let default_value_type = self.compile_static_function_call(scope, default_parameter_value_provider, source_context, Some(&currently_provided_parameter_expressions), true)?;
                    self.coerce_to_expression_type(&default_value_type, &parameter_types[parameter_index].parameter_type, &source_context)?;
                } else {
                    // There is no default value for this argument
                    compiler_bail!(source_context, "Template {} argument at index #{} has no default value, and no explicit value was provided", function.function, parameter_index + 1);
                }
            }
        } else {
            if function.signature.explicit_parameters.is_none() && explicit_arguments.is_some() && !is_synthetic_function_call {
                compiler_bail!(source_context, "Call to data {} does not require any template arguments", function.function);
            } else if function.signature.explicit_parameters.is_some() && explicit_arguments.is_none() {
                compiler_bail!(source_context, "Template {} requires template arguments to be provided for instantiation", function.function);
            }
        }
        let explicit_parameter_count = function.signature.explicit_parameters.as_ref().map(|x| x.len()).unwrap_or(0);

        // Call the function finally with the argument values on the stack
        let function_parameter_count = implicit_parameter_count + explicit_parameter_count;
        self.function_definition.add_variadic_instruction(GospelOpcode::Call, function_parameter_count as u32, Self::get_line_number(source_context)).with_source_context(source_context)?;
        Ok(function.signature.return_value_type.clone())
    }
    fn compile_implicitly_bound_function_closure_or_call(&mut self, scope: &Rc<CompilerLexicalScope>, function: &CompilerFunctionReference, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        // Load the function and the implicit arguments on the stack
        let implicit_parameter_count = self.load_function_and_implicit_arguments(scope, function, source_context)?;

        // If this function has explicit parameters, we have to bind the closure with implicit values and return it directly
        if function.signature.explicit_parameters.is_some() {
            self.function_definition.add_variadic_instruction(GospelOpcode::BindClosure, implicit_parameter_count as u32, Self::get_line_number(source_context)).with_source_context(source_context)?;
            Ok(ExpressionValueType::Closure)
        } else {
            // This function has no implicit parameters, so we can call it immediately to retrieve its value
            self.function_definition.add_variadic_instruction(GospelOpcode::Call, implicit_parameter_count as u32, Self::get_line_number(source_context)).with_source_context(source_context)?;
            Ok(function.signature.return_value_type.clone())
        }
    }
    fn compile_identifier_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &IdentifierExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let resolved_reference = scope.compiler().and_then(|compiler| compiler.resolve_partial_identifier(&expression.identifier, Some(scope.clone())))
            .ok_or_else(|| compiler_error!(source_context, "Failed to resolve identifier {} in scope {}", expression.identifier, scope.full_scope_display_name()))?;

        match resolved_reference {
            CompilerLexicalNode::Declaration(declaration) => {
                if expression.template_arguments.is_some() {
                    compiler_bail!(&source_context, "Did not expect template arguments for local variable, template parameter or global variable access");
                }
                self.compile_lexical_declaration_access(&source_context, &declaration)
            }
            CompilerLexicalNode::Scope(scope_declaration) => {
                match &scope_declaration.class {
                    CompilerLexicalScopeClass::Function(data_closure) => {
                        self.compile_static_function_call(scope, &data_closure.borrow().reference, &source_context, expression.template_arguments.as_ref(), false)
                    }
                    _ => Err(compiler_error!(&source_context, "Scope {} does not name a data or struct declaration", scope_declaration.name))
                }
            }
        }
    }
    fn compile_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &Statement) -> CompilerResult<()> {
        match statement {
            Statement::EmptyStatement(_) => { Ok({}) }
            Statement::WhileLoopStatement(while_loop_statement) => { self.compile_while_loop_statement(scope, &while_loop_statement) }
            Statement::BreakLoopStatement(simple_statement) => { self.compile_break_loop_statement(scope, &*simple_statement) }
            Statement::ContinueLoopStatement(simple_statement) => { self.compile_continue_loop_statement(scope, &*simple_statement) }
            Statement::BlockStatement(block_statement) => { self.compile_block_statement(scope, &*block_statement) }
            Statement::ConditionalStatement(conditional_statement) => { self.compile_conditional_statement(scope, &*conditional_statement) }
            Statement::DeclarationStatement(declaration_statement) => { self.compile_declaration_statement(scope, &*declaration_statement) }
            Statement::AssignmentStatement(assignment_statement) => { self.compile_assignment_statement(scope, &*assignment_statement) }
        }
    }
    fn compile_return_value_expression(&mut self, scope: &Rc<CompilerLexicalScope>, source_context: &ASTSourceContext, expression: &Expression) -> CompilerResult<()> {
        let actual_source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: source_context.clone()};
        let return_value_type = self.compile_expression(scope, expression)?;
        let expected_return_value_type = self.function_signature.return_value_type.clone();
        self.coerce_to_expression_type(&return_value_type, &expected_return_value_type, &actual_source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::SetReturnValue, Self::get_line_number(&actual_source_context)).with_source_context(&actual_source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::Return, Self::get_line_number(&actual_source_context)).with_source_context(&actual_source_context)?;
        Ok({})
    }
    fn compile_assignment_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &AssignmentStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let assignment_identifier = if let Expression::IdentifierExpression(identifier) = &statement.left_hand_expression {
            identifier.identifier.clone()
        } else {
            compiler_bail!(source_context, "Assignment expression left side can only be a partial identifier (got another expression)");
        };
        let resolved_node = scope.compiler().and_then(|compiler| compiler.resolve_partial_identifier(&assignment_identifier, Some(scope.clone())))
            .ok_or_else(|| compiler_error!(source_context, "Failed to resolve partial identifier {}", assignment_identifier))?;

        if let CompilerLexicalNode::Declaration(declaration) = &resolved_node &&
            let CompilerLexicalDeclarationClass::LocalVariable(local_variable) = &declaration.class {

            if let Some(assignment_operator) = statement.assignment_operator {
                // This is a synthetic binary operator assignment, we need to load the old value first, then the new value, and then run a binary operator on them, and write the result to variable
                self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, local_variable.value_slot, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
                let right_side_type = self.compile_expression(scope, &statement.assignment_expression)?;
                let operator_result_type = self.compile_binary_operator(&local_variable.variable_type, &right_side_type, &source_context, assignment_operator)?;

                self.coerce_to_expression_type(&operator_result_type, &local_variable.variable_type, &source_context)?;
                self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, local_variable.value_slot, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            } else {
                // This is a direct assignment
                let right_side_type = self.compile_expression(scope, &statement.assignment_expression)?;
                self.coerce_to_expression_type(&right_side_type, &local_variable.variable_type, &source_context)?;
                self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, local_variable.value_slot, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            }
            Ok({})
        } else {
            compiler_bail!(source_context, "Expected {} to refer to a local variable, but it refers to {} instead", assignment_identifier, resolved_node);
        }
    }
    fn compile_declaration_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &DeclarationStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};

        let slot_index = self.function_definition.add_slot().with_source_context(&source_context)?;
        let local_variable = CompilerLocalVariableDeclaration {value_slot: slot_index, variable_type: statement.value_type.clone()};
        scope.declare(statement.name.as_str(), CompilerLexicalDeclarationClass::LocalVariable(local_variable), DeclarationVisibility::Private, &statement.source_context)?;

        if let Some(variable_initializer) = &statement.initializer {
            let initializer_type = self.compile_expression(scope, variable_initializer)?;
            self.coerce_to_expression_type(&initializer_type, &statement.value_type, &source_context)?;
            self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        }
        Ok({})
    }
    fn compile_conditional_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &ConditionalStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let condition_value_type = self.compile_expression(scope, &statement.condition_expression)?;
        self.coerce_to_bool_type(&condition_value_type, &source_context)?;
        let instruction_encoding = Self::bool_type_instruction_encoding();
        let (_, condition_fixup) = self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let then_scope = scope.declare_scope_generated_name("then", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: then_block_declaration.clone()}), &source_context.line_context)?;
        let then_instruction_index=  self.function_definition.current_instruction_count();
        self.compile_statement(&then_scope, &statement.then_statement)?;

        if let Some(else_statement) = &statement.else_statement {
            // We have an else statement, so we need to jump to the end of the conditional statement after then branch is done
            let (then_instruction_index, then_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch, Self::get_line_number(&source_context)).with_source_context(&then_scope.source_context)?;
            let else_branch_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: then_instruction_index,
                end_instruction_index: else_branch_instruction_index,
            };

            let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
            let else_scope = scope.declare_scope_generated_name("else", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: else_block_declaration.clone()}), &statement.source_context)?;
            self.compile_statement(&else_scope, &else_statement)?;
            else_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: else_branch_instruction_index,
                end_instruction_index: self.function_definition.current_instruction_count(),
            };

            self.function_definition.fixup_control_flow_instruction(condition_fixup, else_branch_instruction_index).with_source_context(&then_scope.source_context)?;
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            self.function_definition.fixup_control_flow_instruction(then_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        } else {
            // No else statement, just fix up condition to jump to the end of then branch if it is zero
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: then_instruction_index,
                end_instruction_index: condition_end_instruction_index,
            };
            self.function_definition.fixup_control_flow_instruction(condition_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        }
        Ok({})
    }
    fn compile_block_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &BlockStatement) -> CompilerResult<()> {
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let block_scope = scope.declare_scope_generated_name("block", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: block_declaration.clone()}), &statement.source_context)?;
        let block_start_instruction_index = self.function_definition.current_instruction_count();
        for inner_statement in &statement.statements {
            self.compile_statement(&block_scope, inner_statement)?;
        }
        block_declaration.borrow_mut().block_range = CompilerInstructionRange{
            start_instruction_index: block_start_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };
        Ok({})
    }
    fn compile_while_loop_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &WhileLoopStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let loop_start_instruction_index = self.function_definition.current_instruction_count();

        let loop_condition_value_type = self.compile_expression(scope, &statement.condition_expression)?;
        self.coerce_to_bool_type(&loop_condition_value_type, &source_context)?;
        let instruction_encoding = Self::bool_type_instruction_encoding();
        let (_, loop_condition_fixup) = self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        let loop_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: Some(CompilerLoopCodegenData::default())}));
        let loop_scope = scope.declare_scope_generated_name("loop", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: loop_declaration.clone()}), &source_context.line_context)?;
        self.compile_statement(&loop_scope, &statement.loop_body_statement)?;

        self.function_definition.add_control_flow_instruction_no_fixup(GospelOpcode::Branch, loop_start_instruction_index, Self::get_line_number(&loop_scope.source_context)).with_source_context(&loop_scope.source_context)?;
        let loop_end_instruction_index = self.function_definition.current_instruction_count();

        self.function_definition.fixup_control_flow_instruction(loop_condition_fixup, loop_end_instruction_index).with_source_context(&loop_scope.source_context)?;
        for loop_start_fixup in &loop_declaration.borrow().loop_codegen_data.as_ref().unwrap().loop_start_fixups {
            self.function_definition.fixup_control_flow_instruction(loop_start_fixup.clone(), loop_start_instruction_index).with_source_context(&loop_scope.source_context)?;
        }
        for loop_finish_fixup in &loop_declaration.borrow().loop_codegen_data.as_ref().unwrap().loop_finish_fixups {
            self.function_definition.fixup_control_flow_instruction(loop_finish_fixup.clone(), loop_end_instruction_index).with_source_context(&loop_scope.source_context)?;
        }
        loop_declaration.borrow_mut().loop_codegen_data = None;
        Ok({})
    }
    fn compile_break_loop_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &SimpleStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let innermost_loop_statement = scope.iterate_scope_chain_inner_first()
            .filter_map(|x| if let CompilerLexicalScopeClass::Block(y) = &x.class { Some(y.clone()) } else { None })
            .find(|x| x.borrow().loop_codegen_data.is_some())
            .ok_or_else(|| compiler_error!(source_context, "break; cannot be used outside the loop body"))?;

        let (_, break_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        innermost_loop_statement.borrow_mut().loop_codegen_data.as_mut().unwrap().loop_finish_fixups.push(break_fixup);
        Ok({})
    }
    fn compile_continue_loop_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &SimpleStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let innermost_loop_statement = scope.iterate_scope_chain_inner_first()
            .filter_map(|x| if let CompilerLexicalScopeClass::Block(y) = &x.class { Some(y.clone()) } else { None })
            .find(|x| x.borrow().loop_codegen_data.is_some())
            .ok_or_else(|| compiler_error!(source_context, "continue; cannot be used outside the loop body"))?;

        let (_, continue_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        innermost_loop_statement.borrow_mut().loop_codegen_data.as_mut().unwrap().loop_start_fixups.push(continue_fixup);
        Ok({})
    }
    fn compile_generic_type_initialization(&mut self, opcode: GospelOpcode, kind_str: &str) -> CompilerResult<u32> {
        let source_context = self.function_scope.source_context.clone();
        let slot_index = self.function_definition.add_slot().with_source_context(&source_context)?;
        let type_name = self.return_value_struct_name.as_ref().ok_or_else(|| compiler_error!(&source_context, "Return value struct name not set on function attempting to allocate UDT layout"))?;

        self.function_definition.add_type_allocate_instruction(opcode, type_name, kind_str, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::SetReturnValue, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok(slot_index)
    }
    fn compile_udt_type_initialization(&mut self, type_kind: UserDefinedTypeKind) -> CompilerResult<u32> {
      self.compile_generic_type_initialization(GospelOpcode::TypeUDTAllocate, type_kind.to_string().as_str())
    }
    fn compile_enum_type_initialization(&mut self, enum_kind: EnumKind) -> CompilerResult<u32> {
        self.compile_generic_type_initialization(GospelOpcode::TypeEnumAllocate, enum_kind.to_string().as_str())
    }
    fn compile_udt_type_metadata_struct_initialization(&mut self) -> CompilerResult<u32> {
        let source_context = self.function_scope.source_context.clone();
        let slot_index = self.function_definition.add_slot().with_source_context(&source_context)?;

        self.function_definition.add_simple_instruction(GospelOpcode::StructAllocate, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok(slot_index)
    }
    fn compile_coerce_alignment_expression(&mut self, scope: &Rc<CompilerLexicalScope>, alignment_expression: &Expression, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        let source_alignment_expression_type = self.compile_expression(scope, alignment_expression)?;

        // Typename is a valid parameter to alignas(T) operator, and should be automatically coerced to the integral alignment
        if source_alignment_expression_type == ExpressionValueType::Typename {
            // TypeCalculateAlignment returns u64, so we do not need to coerce the type
            self.function_definition.add_simple_instruction(GospelOpcode::TypeCalculateAlignment, Self::get_line_number(source_context)).with_source_context(source_context)?;
            Ok(ExpressionValueType::Integer(IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}))
        } else {
            // Should be an integer alignment otherwise
            self.coerce_to_integral_type(&IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &source_alignment_expression_type, false, source_context)
        }
    }
    fn compile_condition_wrapped_expression<S: FnOnce(&mut Self, &Expression, &CompilerSourceContext) -> CompilerResult<()>>(&mut self, scope: &Rc<CompilerLexicalScope>, conditional_declaration: &ExpressionWithCondition, code_generator: S) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: conditional_declaration.source_context.clone()};
        let possibly_jump_to_end_fixup = if let Some(condition_expression) = &conditional_declaration.condition_expression {
            let condition_expression_type = self.compile_expression(scope, condition_expression)?;
            self.coerce_to_bool_type(&condition_expression_type, &source_context)?;
            let instruction_encoding = Self::bool_type_instruction_encoding();
            Some(self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?.1)
        } else { None };

        code_generator(self, &conditional_declaration.expression, &source_context)?;

        if let Some(jump_to_end_fixup) = possibly_jump_to_end_fixup {
            let end_instruction_index = self.function_definition.current_instruction_count();
            self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&source_context)?;
        }
        Ok({})
    }
    fn compile_try_catch_wrapped_statement<T, S: FnOnce(&mut Self, &CompilerSourceContext) -> CompilerResult<T>, R: FnOnce(&mut Self, &CompilerSourceContext) -> CompilerResult<()>>(&mut self, source_context: &CompilerSourceContext, inner_code_generator: S, catch_code_generator: R)  -> CompilerResult<T> {
        let jump_to_exception_handler_fixup = self.function_definition.add_control_flow_instruction(GospelOpcode::PushExceptionHandler, Self::get_line_number(source_context)).with_source_context(source_context)?.1;
        let inner_result = inner_code_generator(self, source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::PopExceptionHandler, Self::get_line_number(source_context)).with_source_context(source_context)?;
        let jump_to_end_fixup = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch, Self::get_line_number(source_context)).with_source_context(source_context)?.1;
        let exception_handler_start_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_exception_handler_fixup, exception_handler_start_instruction_index).with_source_context(source_context)?;
        catch_code_generator(self, source_context)?;
        let end_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(source_context)?;
        Ok(inner_result)
    }
    fn compile_generic_type_mark_partial_statement(&mut self, type_layout_slot_index: u32, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(source_context)).with_source_context(source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::TypeMarkPartial, Self::get_line_number(source_context)).with_source_context(source_context)?;
        Ok({})
    }
    fn compile_udt_type_alignment_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, alignment_expression: &ExpressionWithCondition) -> CompilerResult<()> {
        self.compile_condition_wrapped_expression(scope, alignment_expression, |builder, expression, source_context| {
            builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            let expression_type = builder.compile_coerce_alignment_expression(scope, expression, source_context)?;
            CompilerFunctionBuilder::coerce_to_integral_type(builder, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &expression_type, false, source_context)?;
            builder.function_definition.add_simple_instruction(GospelOpcode::TypeUDTSetUserAlignment, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok({})
        })
    }
    fn compile_udt_type_member_pack_alignment_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, member_pack_alignment_expression: &ExpressionWithCondition) -> CompilerResult<()> {
        self.compile_condition_wrapped_expression(scope, member_pack_alignment_expression, |builder, expression, source_context| {
            builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            let expression_type = builder.compile_expression(scope, expression)?;
            CompilerFunctionBuilder::coerce_to_integral_type(builder, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &expression_type, false, source_context)?;
            builder.function_definition.add_simple_instruction(GospelOpcode::TypeUDTSetMemberPackAlignment, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok({})
        })
    }
    fn compile_udt_type_base_class_statement_inner(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, base_class_expression: &ExpressionWithCondition, is_prototype_pass: bool) -> CompilerResult<()> {
        self.compile_condition_wrapped_expression(scope, base_class_expression, |builder, expression, source_context| {
            builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            let expression_type = builder.compile_expression(scope, expression)?;
            builder.coerce_to_expression_type(&expression_type, &ExpressionValueType::Typename, &source_context)?;
            let base_class_flags = if is_prototype_pass { 1 << 2 } else { 0 };
            builder.function_definition.add_udt_base_class_instruction(base_class_flags, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok({})
        })
    }
    fn compile_udt_type_base_class_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, base_class_expression: &ExpressionWithCondition, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        if is_prototype_pass || allow_partial_types {
            let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: base_class_expression.source_context.clone()};
            self.compile_try_catch_wrapped_statement(&source_context, |inner_builder, _| {
                inner_builder.compile_udt_type_base_class_statement_inner(scope, type_layout_slot_index, base_class_expression, is_prototype_pass)
            }, |inner_builder, source_context| {
                if !is_prototype_pass {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot_index, source_context)?;
                }
                Ok({})
            })
        } else {
            self.compile_udt_type_base_class_statement_inner(scope, type_layout_slot_index, base_class_expression, is_prototype_pass)
        }
    }
    fn compile_enum_underlying_type_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, underlying_type_expression: &ExpressionWithCondition) -> CompilerResult<()> {
        self.compile_condition_wrapped_expression(scope, underlying_type_expression, |inner_builder, underlying_type_expression, source_context| {
            inner_builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            let underlying_expression_type = inner_builder.compile_expression(scope, underlying_type_expression)?;
            inner_builder.coerce_to_expression_type(&underlying_expression_type, &ExpressionValueType::Typename, &source_context)?;
            inner_builder.function_definition.add_simple_instruction(GospelOpcode::TypeEnumSetUnderlyingType, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            Ok({})
        })
    }
    fn compile_enum_constant_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, constant_declaration: &EnumConstantDeclaration) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: constant_declaration.source_context.clone()};
        let possibly_jump_to_end_fixup = if let Some(condition_expression) = &constant_declaration.condition_expression {
            let condition_expression_type = self.compile_expression(scope, condition_expression)?;
            self.coerce_to_bool_type(&condition_expression_type, &source_context)?;
            let instruction_encoding = Self::bool_type_instruction_encoding();
            Some(self.function_definition.add_conditional_branch_instruction(instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?.1)
        } else { None };

        self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        if let Some(explicit_constant_value) = &constant_declaration.value_expression {
            let value_expression_type = self.compile_expression(scope, explicit_constant_value)?;
            let integral_value_type = CompilerFunctionBuilder::check_integral_type(&value_expression_type, &source_context)?;
            let instruction_encoding = CompilerFunctionBuilder::integral_type_instruction_encoding(&integral_value_type);
            self.function_definition.add_enum_constant_with_value_instruction(constant_declaration.name.as_ref(), 0, instruction_encoding, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        } else {
            self.function_definition.add_type_member_instruction(GospelOpcode::TypeEnumAddConstant, constant_declaration.name.as_ref(), 0, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        }

        if let Some(jump_to_end_fixup) = possibly_jump_to_end_fixup {
            let end_instruction_index = self.function_definition.current_instruction_count();
            self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&source_context)?;
        }
        Ok({})
    }
    fn compile_enum_constant_prototype_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, constant_declaration: &EnumConstantDeclaration) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: constant_declaration.source_context.clone()};
        self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        let constant_flags: u32 = 1 << 2;
        self.function_definition.add_type_member_instruction(GospelOpcode::TypeEnumAddConstant, constant_declaration.name.as_ref(), constant_flags, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok({})
    }
    fn compile_generic_type_layout_finalization(&mut self, type_layout_slot_index: u32, type_layout_metadata_slot_index: Option<u32>, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        if let Some(metadata_slot_index) = type_layout_metadata_slot_index {
            self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, metadata_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
            self.function_definition.add_simple_instruction(GospelOpcode::TypeUDTAttachMetadata, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        }
        self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot_index, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        self.function_definition.add_simple_instruction(GospelOpcode::TypeFinalize, Self::get_line_number(&source_context)).with_source_context(&source_context)?;

        self.function_definition.add_simple_instruction(GospelOpcode::Return, Self::get_line_number(&source_context)).with_source_context(&source_context)?;
        Ok({})
    }
    fn get_line_number(source_context: &CompilerSourceContext) -> i32 {
        source_context.line_context.line_number as i32
    }
    fn commit(self) -> CompilerResult<()> {
        let codegen_data = self.function_scope.module_codegen().ok_or_else(|| compiler_error!(&self.function_scope.source_context, "Codegen not found for current module"))?;
        if let Err(error) = codegen_data.visitor.borrow_mut().define_function(self.function_name, self.function_definition) {
            compiler_bail!(&self.function_scope.source_context, "Failed to define function {}: {}", self.function_scope.full_scope_name_no_module_name(), error.to_string());
        }
        Ok({})
    }
}

trait CompilerModuleBuilderInternal : Debug {
    fn module_scope(&self) -> &Rc<CompilerLexicalScope>;
}

#[allow(private_bounds)]
pub trait CompilerModuleBuilder : CompilerModuleBuilderInternal {
    fn add_source_file(&self, source_file: ModuleSourceFile) -> CompilerResult<()> {
        let file_name_without_extension = PathBuf::from(source_file.file_name.as_str()).file_stem().map(|x| x.to_string_lossy().to_string()).unwrap();
        let file_scope = self.module_scope().declare_scope(&file_name_without_extension, CompilerLexicalScopeClass::SourceFile(CompilerSourceFileData{file_name: source_file.file_name.clone()}), DeclarationVisibility::Public, &ASTSourceContext::default())?;

        source_file.declarations.iter().map(|top_level_declaration| match top_level_declaration {
            TopLevelDeclaration::EmptyStatement => { Ok({}) }
            TopLevelDeclaration::ImportStatement(import_statement) => { CompilerInstance::pre_compile_import_statement(&file_scope, import_statement) }
            TopLevelDeclaration::InputStatement(extern_statement) => { CompilerInstance::compile_input_statement(&file_scope, extern_statement) }
            TopLevelDeclaration::NamespaceStatement(namespace_statement) => { CompilerInstance::compile_namespace_statement(&file_scope, namespace_statement, DeclarationVisibility::Public) }
            TopLevelDeclaration::DataStatement(data_statement) => { CompilerInstance::pre_compile_data_statement(&file_scope, data_statement, DeclarationVisibility::Public)?; Ok({}) }
            TopLevelDeclaration::StructStatement(struct_statement) => { CompilerInstance::compile_struct_statement(&file_scope, struct_statement, None, DeclarationVisibility::Public)?; Ok({}) }
            TopLevelDeclaration::EnumStatement(enum_statement) => { CompilerInstance::pre_compile_enum_statement(&file_scope, enum_statement, None, DeclarationVisibility::Public)?; Ok({}) }
        }).chain_compiler_result(|| compiler_error!(&file_scope.source_context, "Failed to compile source file"))
    }
    fn add_simple_function(&self, function_name: &str, return_value_type: ExpressionValueType, expression: &Expression) -> CompilerResult<GospelSourceObjectReference> {
        let source_context = CompilerSourceContext::default();
        let (function_scope, function_closure) = CompilerInstance::declare_function(
            &self.module_scope(), function_name, DeclarationVisibility::Public, return_value_type, None, false, &source_context.line_context)?;

        if let Some(module_codegen_data) = self.module_scope().module_codegen() {
            module_codegen_data.push_delayed_function_definition(&function_scope, Box::new(CompilerSimpleExpressionFunctionGenerator{
                source_context: source_context.line_context.clone(),
                return_value_expression: expression.clone(),
            }))?;
        }
        Ok(function_closure.borrow().reference.function.clone())
    }
}

#[derive(Debug)]
pub struct CompilerModuleDeclarationBuilder {
    module_scope: Rc<CompilerLexicalScope>,
    /// This is not actually "dead code", this ensures that the compile instances lives as long as the reference to the module scope, which itself does not keep a hard reference to the compiler
    #[allow(dead_code)]
    compiler: Rc<CompilerInstance>,
}
impl CompilerModuleBuilderInternal for CompilerModuleDeclarationBuilder {
    fn module_scope(&self) -> &Rc<CompilerLexicalScope> {
        &self.module_scope
    }
}
impl CompilerModuleBuilder for CompilerModuleDeclarationBuilder {}

#[derive(Debug)]
pub struct CompilerModuleDefinitionBuilder {
    module_scope: Rc<CompilerLexicalScope>,
    container_builder: RefCell<Option<Rc<RefCell<dyn GospelContainerBuilder>>>>,
    /// This is not actually "dead code", this ensures that the compile instances lives as long as the reference to the module scope, which itself does not keep a hard reference to the compiler
    #[allow(dead_code)]
    compiler: Rc<CompilerInstance>,
}
impl CompilerModuleDefinitionBuilder {
    fn add_compiler_builtin_source_code(&self) -> CompilerResult<()> {
        // Parse internal compiler code automatically inlined into every module
        let sys_source_code = parse_source_file("compiler_rt/sys.gs", include_str!("../res/compiler_rt/sys.gs"))
            .map_err(|x| compiler_error!(&self.module_scope.source_context, "Internal compiler error: {}", x))?;
        self.add_source_file(sys_source_code)?;
        Ok({})
    }
    pub fn compile(&self) -> CompilerResult<GospelContainer> {
        if let CompilerLexicalScopeClass::Module(module_data) = &self.module_scope.class &&
            let Some(module_codegen_data) = { module_data.codegen_data.borrow().clone() } &&
            let Some(module_container_builder) = { self.container_builder.borrow().clone() } {

            // Add compiler generated code to the module
            self.add_compiler_builtin_source_code()?;
            // Compile imports before we start compiling function definitions
            module_codegen_data.compile_import_statements(&self.module_scope.source_context)?;
            // Compile function definitions now that we have resolved all imports
            module_codegen_data.compile_function_definitions(&self.module_scope.source_context)?;
            // We are done now, so build the resulting module container
            let result_container = module_container_builder.borrow_mut().build().with_source_context(&self.module_scope.source_context)?;

            // Cleanup code generation data on the module and release module builder
            *module_data.codegen_data.borrow_mut() = None;
            *self.container_builder.borrow_mut() = None;
            Ok(result_container)
        } else {
            Err(compiler_error!(&self.module_scope.source_context, "Cannot compile module because it has already been compiled"))
        }
    }
}
impl CompilerModuleBuilderInternal for CompilerModuleDefinitionBuilder {
    fn module_scope(&self) -> &Rc<CompilerLexicalScope> {
        &self.module_scope
    }
}
impl CompilerModuleBuilder for CompilerModuleDefinitionBuilder {}

#[derive(Debug, Clone)]
struct CompilerSimpleExpressionFunctionGenerator {
    source_context: ASTSourceContext,
    return_value_expression: Expression,
}
impl CompilerFunctionCodeGenerator for CompilerSimpleExpressionFunctionGenerator {
    fn generate(&self, function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<()> {
        let mut function_builder = CompilerFunctionBuilder::create(function_scope)?;
        function_builder.compile_return_value_expression(&function_builder.function_scope.clone(), &self.source_context, &self.return_value_expression)?;
        function_builder.commit()
    }
}

trait CompilerStructFragmentGenerator : Debug {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()>;
}

#[derive(Debug)]
struct CompilerStructBlockFragment {
    block_declaration: Rc<RefCell<CompilerBlockDeclaration>>,
    fragments: Vec<Box<dyn CompilerStructFragmentGenerator>>
}
impl CompilerStructFragmentGenerator for CompilerStructBlockFragment {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        let block_instruction_index = builder.function_definition.current_instruction_count();
        for inner_declaration in &self.fragments {
            inner_declaration.compile_fragment(builder, type_layout_slot, type_layout_metadata_slot, is_prototype_pass, allow_partial_types)?;
        }
        self.block_declaration.borrow_mut().block_range = CompilerInstructionRange{
            start_instruction_index: block_instruction_index,
            end_instruction_index: builder.function_definition.current_instruction_count(),
        };
        Ok({})
    }
}

#[derive(Debug)]
struct CompilerStructConditionalFragment {
    source_context: CompilerSourceContext,
    scope: Rc<CompilerLexicalScope>,
    condition_expression: Expression,
    then_block_declaration: Rc<RefCell<CompilerBlockDeclaration>>,
    then_fragment: Box<dyn CompilerStructFragmentGenerator>,
    else_branch: Option<(Rc<RefCell<CompilerBlockDeclaration>>, Box<dyn CompilerStructFragmentGenerator>)>,
}
impl CompilerStructConditionalFragment {
    fn compile_full_pass_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, allow_partial_types: bool) -> CompilerResult<()> {
        let mut partial_type_jump_to_end_fixup: Option<GospelJumpLabelFixup> = None;
        if allow_partial_types {
            builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, source_context| {
                let condition_value_type = inner_builder.compile_expression(&self.scope, &self.condition_expression)?;
                CompilerFunctionBuilder::coerce_to_bool_type(inner_builder, &condition_value_type, &source_context)?;
                Ok({})
            }, |inner_builder, source_context| {
                // If we failed to evaluate the condition, we do not run either branches, and just jump to the end of this fragment. Type layout in this case becomes partial
                inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot, source_context)?;
                partial_type_jump_to_end_fixup = Some(inner_builder.function_definition.add_control_flow_instruction(GospelOpcode::Branch, CompilerFunctionBuilder::get_line_number(source_context)).with_source_context(source_context)?.1);
                Ok({})
            })?
        } else {
            let condition_value_type = builder.compile_expression(&self.scope, &self.condition_expression)?;
            CompilerFunctionBuilder::coerce_to_bool_type(builder, &condition_value_type, &self.source_context)?;
        };
        let instruction_encoding = CompilerFunctionBuilder::bool_type_instruction_encoding();
        let (_, condition_fixup) = builder.function_definition.add_conditional_branch_instruction(instruction_encoding, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;

        let then_branch_instruction_index = builder.function_definition.current_instruction_count();
        self.then_fragment.compile_fragment(builder, type_layout_slot, type_layout_metadata_slot, false, allow_partial_types)?;

        if let Some((else_block_declaration, else_fragment)) = &self.else_branch {
            // We have an else statement, so we need to jump to the end of the conditional statement after then branch is done
            let (_, then_fixup) = builder.function_definition.add_control_flow_instruction(GospelOpcode::Branch, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            let else_branch_instruction_index = builder.function_definition.current_instruction_count();
            self.then_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: then_branch_instruction_index,
                end_instruction_index: else_branch_instruction_index,
            };
            else_fragment.compile_fragment(builder, type_layout_slot, type_layout_metadata_slot, false, allow_partial_types)?;
            else_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: else_branch_instruction_index,
                end_instruction_index: builder.function_definition.current_instruction_count(),
            };

            builder.function_definition.fixup_control_flow_instruction(condition_fixup, else_branch_instruction_index).with_source_context(&self.source_context)?;
            let condition_end_instruction_index = builder.function_definition.current_instruction_count();
            builder.function_definition.fixup_control_flow_instruction(then_fixup, condition_end_instruction_index).with_source_context(&self.source_context)?;
        } else {
            // No else statement, just fix up condition to jump to the end of then branch if it is zero
            let condition_end_instruction_index = builder.function_definition.current_instruction_count();
            self.then_block_declaration.borrow_mut().block_range = CompilerInstructionRange{
                start_instruction_index: then_branch_instruction_index,
                end_instruction_index: condition_end_instruction_index,
            };
            builder.function_definition.fixup_control_flow_instruction(condition_fixup, condition_end_instruction_index).with_source_context(&self.source_context)?;
        }
        if let Some(jump_to_end_fixup) = partial_type_jump_to_end_fixup {
            let end_instruction_index = builder.function_definition.current_instruction_count();
            builder.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&self.source_context)?;
        }
        Ok({})
    }
    fn compile_prototype_pass_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, allow_partial_types: bool) -> CompilerResult<()> {
        // Prototype pass does not need to evaluate conditions, both branches contribute to the struct prototype
        self.then_fragment.compile_fragment(builder, type_layout_slot, type_layout_metadata_slot, true, allow_partial_types)?;
        if let Some((_, else_fragment)) = &self.else_branch {
            else_fragment.compile_fragment(builder, type_layout_slot, type_layout_metadata_slot, true, allow_partial_types)?;
        }
        Ok({})
    }
}
impl CompilerStructFragmentGenerator for CompilerStructConditionalFragment {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
       if is_prototype_pass {
           self.compile_prototype_pass_fragment(builder, type_layout_slot, type_layout_metadata_slot, allow_partial_types)
       } else {
           self.compile_full_pass_fragment(builder, type_layout_slot, type_layout_metadata_slot, allow_partial_types)
       }
    }
}

#[derive(Debug)]
struct CompilerStructMetadataFragment {
    source_context: CompilerSourceContext,
    scope: Rc<CompilerLexicalScope>,
    metadata_function_reference: CompilerFunctionReference,
    metadata_name: String,
}
impl CompilerStructMetadataFragment {
    fn compile_full_pass_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_metadata_slot: u32, allow_take_slot: bool) -> CompilerResult<()> {
        // We cannot use TakeSlot if result of our calculation can be lost due to an exception
        if allow_take_slot {
            // Take metadata struct from the slot
            builder.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_metadata_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        } else {
            // Copy metadata struct from the slot
            builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_metadata_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        }
        // Push the struct closure or resolved type layout on the stack
        builder.compile_implicitly_bound_function_closure_or_call(&self.scope, &self.metadata_function_reference, &self.source_context)?;

        // Set the meta struct field value and store the struct back to the slot
        builder.function_definition.add_string_instruction(GospelOpcode::StructSetField, self.metadata_name.as_str(), CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        builder.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, type_layout_metadata_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        Ok({})
    }
}
impl CompilerStructFragmentGenerator for CompilerStructMetadataFragment {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        // Prototype pass does not require metadata generation
        if !is_prototype_pass {
            if allow_partial_types {
                builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _| {
                    self.compile_full_pass_fragment(inner_builder, type_layout_metadata_slot, !allow_partial_types)?;
                    Ok({})
                }, |inner_builder, source_context| {
                    // Type without complete metadata is also considered incomplete
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot, source_context)?;
                    Ok({})
                })?;
            } else {
                self.compile_full_pass_fragment(builder, type_layout_metadata_slot, !allow_partial_types)?;
            }
        }
        Ok({})
    }
}

#[derive(Debug)]
struct CompilerStructMemberFragment {
    source_context: CompilerSourceContext,
    scope: Rc<CompilerLexicalScope>,
    member_name: Option<String>,
    member_type_expression: Expression,
    alignment_expression: Option<ExpressionWithCondition>,
    array_size_expression: Option<Expression>,
    bitfield_width_expression: Option<Expression>,
}
impl CompilerStructMemberFragment {
    fn compile_member_alignment_statement(&self, builder: &mut CompilerFunctionBuilder, alignment_expression: &ExpressionWithCondition) -> CompilerResult<()> {
        builder.compile_condition_wrapped_expression(&self.scope, alignment_expression, |builder, expression, source_context| {
            builder.function_definition.add_simple_instruction(GospelOpcode::Pop, CompilerFunctionBuilder::get_line_number(source_context)).with_source_context(source_context)?;
            let alignment_expression_type = builder.compile_coerce_alignment_expression(&self.scope, expression, &self.source_context)?;
            CompilerFunctionBuilder::coerce_to_integral_type(builder, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &alignment_expression_type, false, &self.source_context)?;
            Ok({})
        })
    }
    fn compile_full_member_declaration(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;

        // Compile member type expression
        let member_type_expression_type = builder.compile_expression(&self.scope, &self.member_type_expression)?;
        let member_flags = if is_prototype_pass { 1 << 2 } else { 0 } as u32;
        builder.coerce_to_expression_type(&member_type_expression_type, &ExpressionValueType::Typename, &self.source_context)?;

        if let Some(bitfield_width_expression) = &self.bitfield_width_expression {
            // If there is a bitfield width expression, this is a bitfield member
            let bitfield_width_expression_type = builder.compile_expression(&self.scope, bitfield_width_expression)?;
            CompilerFunctionBuilder::coerce_to_integral_type(builder, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &bitfield_width_expression_type, false, &self.source_context)?;
            builder.function_definition.add_type_member_instruction(GospelOpcode::TypeUDTAddBitfield, self.member_name.as_ref(), member_flags, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        } else {
            // If array size expression is present, we need to convert the given member type to an array implicitly
            if let Some(array_size_expression) = &self.array_size_expression {
                let array_size_expression_type = builder.compile_expression(&self.scope, array_size_expression)?;
                CompilerFunctionBuilder::coerce_to_integral_type(builder, &IntegralType {bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned}, &array_size_expression_type, false, &self.source_context)?;
                builder.function_definition.add_simple_instruction(GospelOpcode::TypeArrayCreate, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            }

            // Generate alignment expression if we have one provided, otherwise pass -1 to indicate no user specified alignment
            builder.function_definition.add_int64_constant_instruction(-1i64 as u64, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            if let Some(alignment_expression) = &self.alignment_expression {
                if is_prototype_pass || allow_partial_types {
                    builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _source_context| {
                        self.compile_member_alignment_statement(inner_builder, alignment_expression)
                    }, |inner_builder, source_context| {
                        if !is_prototype_pass {
                            inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot, source_context)
                        } else { Ok({}) }
                    })?;
                } else {
                    self.compile_member_alignment_statement(builder, alignment_expression)?;
                }
            }
            builder.function_definition.add_type_member_instruction(GospelOpcode::TypeUDTAddField, self.member_name.as_ref(), member_flags, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        }
        Ok({})
    }
    fn compile_simplified_member_declaration(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, is_prototype_pass: bool) -> CompilerResult<()> {
        builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;

        // Simplified type of the expression is void, and simplified declarations are only allowed as prototypes
        builder.function_definition.add_string_instruction(GospelOpcode::TypePrimitiveCreate, PrimitiveType::Void.to_string().as_str(), CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        let member_flags = if is_prototype_pass { (1 << 2) as u32 } else { 0 };
        if self.bitfield_width_expression.is_some() {
            builder.function_definition.add_type_member_instruction(GospelOpcode::TypeUDTAddBitfield, self.member_name.as_ref(), member_flags,
                                                                    CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        } else {
            builder.function_definition.add_int64_constant_instruction(-1i64 as u64, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            builder.function_definition.add_type_member_instruction(GospelOpcode::TypeUDTAddField, self.member_name.as_ref(), member_flags,
                                                                    CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        }
        Ok({})
    }
}
impl CompilerStructFragmentGenerator for CompilerStructMemberFragment {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, _type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        if is_prototype_pass || allow_partial_types {
            builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _| {
                self.compile_full_member_declaration(inner_builder, type_layout_slot, is_prototype_pass, allow_partial_types)
            }, |inner_builder, source_context| {
                self.compile_simplified_member_declaration(inner_builder, type_layout_slot, is_prototype_pass)?;
                if !is_prototype_pass {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot, source_context)
                } else { Ok({}) }
            })
        } else {
            self.compile_full_member_declaration(builder, type_layout_slot, false, false)
        }
    }
}

#[derive(Debug)]
struct CompilerStructVirtualFunctionFragment {
    source_context: CompilerSourceContext,
    scope: Rc<CompilerLexicalScope>,
    function_name: String,
    return_type_expression: Expression,
    parameters: Vec<FunctionParameterDeclaration>,
    constant: bool,
    is_override: bool,
}
impl CompilerStructVirtualFunctionFragment {
    fn compile_full_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, is_prototype_pass: bool) -> CompilerResult<()> {
        builder.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, type_layout_slot, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;

        let return_value_expression_type = builder.compile_expression(&self.scope, &self.return_type_expression)?;
        builder.coerce_to_expression_type(&return_value_expression_type, &ExpressionValueType::Typename, &self.source_context)?;
        let function_flags = (if self.constant { 1 << 0 } else { 0 }) | (if self.is_override { 1 << 1 } else { 0 }) | (if is_prototype_pass { 1 << 2 } else { 0 });

        for argument_index in 0..self.parameters.len() {
            let argument_expression_type = builder.compile_expression(&self.scope, &self.parameters[argument_index].parameter_type)?;
            builder.coerce_to_expression_type(&argument_expression_type, &ExpressionValueType::Typename, &self.source_context)?;

            if let Some(argument_name) = &self.parameters[argument_index].parameter_name {
                let argument_name_index = builder.function_definition.add_string_reference_internal(argument_name.as_str());
                builder.function_definition.add_int_instruction(GospelOpcode::Int32Constant, argument_name_index, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            } else {
                builder.function_definition.add_int_instruction(GospelOpcode::Int32Constant, -1i32 as u32, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
            }
        }
        builder.function_definition.add_udt_virtual_function_instruction(self.function_name.as_str(), function_flags, (self.parameters.len() * 2) as u32, CompilerFunctionBuilder::get_line_number(&self.source_context)).with_source_context(&self.source_context)?;
        Ok({})
    }
}
impl CompilerStructFragmentGenerator for CompilerStructVirtualFunctionFragment {
    fn compile_fragment(&self, builder: &mut CompilerFunctionBuilder, type_layout_slot: u32, _type_layout_metadata_slot: u32, is_prototype_pass: bool, allow_partial_types: bool) -> CompilerResult<()> {
        if is_prototype_pass || allow_partial_types {
            builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _| {
                self.compile_full_fragment(inner_builder, type_layout_slot, is_prototype_pass)
            }, |inner_builder, source_context| {
                if !is_prototype_pass {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot, source_context)?;
                }
                // Simplified virtual function declarations are not feasible due to the fact that virtual functions can be overloaded and name alone is not enough to identify them,
                // as well as the fact that virtual functions require precise type information to generate callable thunks for them
                Ok({})
            })
        } else {
            self.compile_full_fragment(builder, type_layout_slot, false)
        }
    }
}

#[derive(Debug)]
struct BlankStructFragmentGenerator {}
impl CompilerStructFragmentGenerator for BlankStructFragmentGenerator {
    fn compile_fragment(&self, _builder: &mut CompilerFunctionBuilder, _type_layout_slot: u32, _type_layout_metadata_slot: u32, _is_prototype_pass: bool, _allow_partial_types: bool) -> CompilerResult<()> {
        Ok({})
    }
}

#[derive(Debug)]
struct CompilerStructFunctionGenerator {
    struct_kind: UserDefinedTypeKind,
    alignment_expression: Option<ExpressionWithCondition>,
    member_pack_alignment_expression: Option<ExpressionWithCondition>,
    base_class_expressions: Vec<ExpressionWithCondition>,
    allow_partial_types: bool,
    generate_prototype_layout: bool,
    source_context: CompilerSourceContext,
    fragments: Vec<Box<dyn CompilerStructFragmentGenerator>>,
}
impl CompilerFunctionCodeGenerator for CompilerStructFunctionGenerator {
    fn generate(&self, function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<()> {
        let mut function_builder = CompilerFunctionBuilder::create(function_scope)?;

        let type_layout_slot_index = function_builder.compile_udt_type_initialization(self.struct_kind)?;
        let type_layout_metadata_slot_index = function_builder.compile_udt_type_metadata_struct_initialization()?;

        if let Some(alignment_expression) = &self.alignment_expression {
            if self.allow_partial_types {
                function_builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _source_context| {
                    inner_builder.compile_udt_type_alignment_expression(&inner_builder.function_scope.clone(), type_layout_slot_index, alignment_expression)
                }, |inner_builder, source_context| {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot_index, source_context)
                })?;
            } else {
                function_builder.compile_udt_type_alignment_expression(&function_builder.function_scope.clone(), type_layout_slot_index, alignment_expression)?;
            }
        }
        if let Some(member_pack_alignment_expression) = &self.member_pack_alignment_expression {
            function_builder.compile_udt_type_member_pack_alignment_expression(&function_builder.function_scope.clone(), type_layout_slot_index, member_pack_alignment_expression)?;
        }
        for base_class_expression in &self.base_class_expressions {
            function_builder.compile_udt_type_base_class_expression(&function_builder.function_scope.clone(), type_layout_slot_index, base_class_expression, false, self.allow_partial_types)?;
        }
        // Main pass with UDT layout generation
        self.fragments.iter().map(|struct_fragment| {
            struct_fragment.compile_fragment(&mut function_builder, type_layout_slot_index, type_layout_metadata_slot_index, false, self.allow_partial_types)
        }).chain_compiler_result(|| compiler_error!(&self.source_context, "Failed to compile struct definition (main pass)"))?;

        // Optional secondary pass that generates layout prototype information useful to some users
        if self.generate_prototype_layout {
            self.fragments.iter().map(|struct_fragment| {
                struct_fragment.compile_fragment(&mut function_builder, type_layout_slot_index, type_layout_metadata_slot_index, true, false)
            }).chain_compiler_result(|| compiler_error!(&self.source_context, "Failed to compile struct definition (prototype pass)"))?;
            for base_class_expression in &self.base_class_expressions {
                function_builder.compile_udt_type_base_class_expression(&function_builder.function_scope.clone(), type_layout_slot_index, base_class_expression, true, false)?;
            }
        }
        function_builder.compile_generic_type_layout_finalization(type_layout_slot_index, Some(type_layout_metadata_slot_index), &self.source_context)?;
        function_builder.commit()
    }
}

#[derive(Debug)]
struct CompilerEnumFunctionGenerator {
    enum_kind: EnumKind,
    underlying_type_expression: Option<ExpressionWithCondition>,
    allow_partial_types: bool,
    generate_prototype_layout: bool,
    source_context: CompilerSourceContext,
    constants: Vec<EnumConstantDeclaration>,
}
impl CompilerFunctionCodeGenerator for CompilerEnumFunctionGenerator {
    fn generate(&self, function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<()> {
        let mut function_builder = CompilerFunctionBuilder::create(function_scope)?;
        let type_layout_slot_index = function_builder.compile_enum_type_initialization(self.enum_kind)?;

        if let Some(underlying_type_expression) = &self.underlying_type_expression {
            if self.allow_partial_types {
                function_builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _source_context| {
                    inner_builder.compile_enum_underlying_type_expression(&inner_builder.function_scope.clone(), type_layout_slot_index, underlying_type_expression)
                }, |inner_builder, source_context| {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot_index, source_context)
                })?;
            } else {
                function_builder.compile_enum_underlying_type_expression(&function_builder.function_scope.clone(), type_layout_slot_index, underlying_type_expression)?;
            }
        }

        for enum_constant in &self.constants {
            if self.allow_partial_types {
                function_builder.compile_try_catch_wrapped_statement(&self.source_context, |inner_builder, _source_context| {
                    inner_builder.compile_enum_constant_declaration(&inner_builder.function_scope.clone(), type_layout_slot_index, enum_constant)
                }, |inner_builder, source_context| {
                    inner_builder.compile_generic_type_mark_partial_statement(type_layout_slot_index, source_context)
                })?;
            } else {
                function_builder.compile_enum_constant_declaration(&function_builder.function_scope.clone(), type_layout_slot_index, enum_constant)?;
            }
        }

        if self.generate_prototype_layout {
            for enum_constant in &self.constants {
                function_builder.compile_enum_constant_prototype_declaration(&function_builder.function_scope.clone(), type_layout_slot_index, enum_constant)?;
            }
        }
        function_builder.compile_generic_type_layout_finalization(type_layout_slot_index, None, &self.source_context)?;
        function_builder.commit()
    }
}

impl CompilerInstance {
    pub fn create(options: CompilerOptions) -> Rc<CompilerInstance> {
        Rc::new(CompilerInstance{compiler_options: options, module_scopes: RefCell::new(HashMap::new())})
    }
    pub fn declare_module(self: &Rc<Self>, module_name: &str) -> CompilerResult<CompilerModuleDeclarationBuilder> {
        let source_context = CompilerSourceContext::default();
        if self.module_scopes.borrow().contains_key(module_name) {
            compiler_bail!(source_context, "Module {} has previously been declared or defined", module_name);
        }
        let new_module_scope = CompilerLexicalScope::create_module_scope(self, module_name.to_string(), &source_context, None);
        self.module_scopes.borrow_mut().insert(module_name.to_string(), new_module_scope.clone());
        Ok(CompilerModuleDeclarationBuilder{module_scope: new_module_scope, compiler: self.clone()})
    }
    pub fn define_module(self: &Rc<Self>, module_name: &str) -> CompilerResult<CompilerModuleDefinitionBuilder> {
        let source_context = CompilerSourceContext::default();
        if self.module_scopes.borrow().contains_key(module_name) {
            compiler_bail!(source_context, "Module {} has previously been declared or defined", module_name);
        }
        let container_writer = Rc::new(RefCell::new(GospelContainerWriter::create(module_name)));
        let new_module_scope = CompilerLexicalScope::create_module_scope(self, module_name.to_string(), &source_context, Some(container_writer.clone()));
        self.module_scopes.borrow_mut().insert(module_name.to_string(), new_module_scope.clone());
        Ok(CompilerModuleDefinitionBuilder{module_scope: new_module_scope, compiler: self.clone(), container_builder: RefCell::new(Some(container_writer))})
    }
    pub fn find_module_scope(self: &Rc<Self>, module_name: &str) -> Option<Rc<CompilerLexicalScope>> {
        self.module_scopes.borrow().get(module_name).cloned()
    }
    fn resolve_absolute_identifier(&self, identifier: &PartialIdentifier, visibility_context: Option<&DeclarationVisibilityContext>) -> Option<CompilerLexicalNode> {
        if identifier.kind == PartialIdentifierKind::ModuleRelative {
            if let Some(module_name) = visibility_context.and_then(|x| x.module_name.as_ref()) {
                if let Some(module_scope) = self.module_scopes.borrow().get(module_name) {
                    let module_relative_identifier = PartialIdentifier{kind: PartialIdentifierKind::Relative, path: identifier.path.clone()};
                    return module_scope.resolve_relative_identifier(&module_relative_identifier, visibility_context, false);
                }
            }
        } else {
            if let Some(module_name) = identifier.path.first() {
                if let Some(module_scope) = self.module_scopes.borrow().get(module_name) {
                    let module_relative_identifier = PartialIdentifier{kind: PartialIdentifierKind::Relative, path: identifier.path.iter().cloned().skip(1).collect()};
                    return module_scope.resolve_relative_identifier(&module_relative_identifier, visibility_context, false);
                }
            }
        }
        None
    }
    fn resolve_partial_identifier(&self, identifier: &PartialIdentifier, scope: Option<Rc<CompilerLexicalScope>>) -> Option<CompilerLexicalNode> {
        let visibility_context = scope.as_ref().map(|x| x.visibility_context());

        // Attempt to resolve relative to the provided scope or relative to its parent scope
        if identifier.kind == PartialIdentifierKind::Relative {
            let mut maybe_current_scope = scope;
            while let Some(current_scope) = maybe_current_scope {
                // Check if we can resolve identifier from the current scope
                if let Some(result_reference) = current_scope.resolve_relative_identifier(identifier, visibility_context.as_ref(), true) {
                    return Some(result_reference);
                }
                // Try to resolve it from the parent scope of the current scope
                maybe_current_scope = current_scope.parent.clone().and_then(|x| x.upgrade());
            }
        }
        // Relative resolution failed or this is an absolute identifier, try to resolve as absolute identifier
        self.resolve_absolute_identifier(identifier, visibility_context.as_ref())
    }
    fn convert_access_specifier(value_type: DeclarationAccessSpecifier) -> DeclarationVisibility {
        match value_type {
            DeclarationAccessSpecifier::Public => DeclarationVisibility::Public,
            DeclarationAccessSpecifier::Internal => DeclarationVisibility::ModuleInternal,
            DeclarationAccessSpecifier::Local => DeclarationVisibility::FileLocal,
        }
    }
    fn pre_compile_import_statement(scope: &Rc<CompilerLexicalScope>, statement: &ImportStatement) -> CompilerResult<()> {
        // Right now import statements have no effect outside the module definitions since they are only resolved within function and struct bodies, so discard them if the current module is not generating any code
        if let Some(module_codegen_data) = scope.module_codegen() {
            module_codegen_data.push_delayed_import(scope, statement)
        } else { Ok({}) }
    }
    fn compile_import_statement(scope: &Rc<CompilerLexicalScope>, statement: &ImportStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};

        // Imports are resolved against a scope with only module name, so they cannot access file local or scope local declarations from any files, including the one we are currently compiling
        // They are still resolved against the module name to allow using module relative identifier syntax and accessing individual module-local files for the current module
        let import_visibility_context = DeclarationVisibilityContext{ module_name: Some(scope.module_name()), file_name: None, source_scope: None };
        match &statement.statement_type {
            ModuleImportStatementType::QualifiedImport(qualified_import) => {
                if let Some(imported_node) = scope.compiler().and_then(|compiler| compiler.resolve_absolute_identifier(&qualified_import, Some(&import_visibility_context))) {
                    match &imported_node {
                        CompilerLexicalNode::Scope(imported_scope) => {
                            scope.declare(imported_node.node_name(), CompilerLexicalDeclarationClass::NamespaceImport(Rc::downgrade(&imported_scope)), DeclarationVisibility::Private, &source_context.line_context)?;
                        }
                        CompilerLexicalNode::Declaration(imported_decl) => {
                            scope.declare(imported_node.node_name(), CompilerLexicalDeclarationClass::Import(Rc::downgrade(&imported_decl)), DeclarationVisibility::Private, &source_context.line_context)?;
                        }
                    };
                    Ok({})
                } else {
                    Err(compiler_error!(&source_context, "Failed to resolve qualified import {}", qualified_import))
                }
            }
            ModuleImportStatementType::CompositeImport(composite_import) => {
                let resolved_namespace_import = scope.compiler().and_then(|compiler| compiler.resolve_absolute_identifier(&composite_import.namespace, Some(&import_visibility_context)));
                if let Some(imported_node) = resolved_namespace_import {
                    if let CompilerLexicalNode::Scope(imported_namespace) = imported_node {
                        for imported_node_name in &composite_import.imported_names {
                            if let Some(imported_node) = imported_namespace.find_unique_child_check_access(imported_node_name, Some(&import_visibility_context)) {
                                match &imported_node {
                                    CompilerLexicalNode::Scope(imported_scope) => {
                                        scope.declare(imported_node.node_name(), CompilerLexicalDeclarationClass::NamespaceImport(Rc::downgrade(&imported_scope)), DeclarationVisibility::Private, &source_context.line_context)?;
                                    }
                                    CompilerLexicalNode::Declaration(imported_decl) => {
                                        scope.declare(imported_node.node_name(), CompilerLexicalDeclarationClass::Import(Rc::downgrade(&imported_decl)), DeclarationVisibility::Private, &source_context.line_context)?;
                                    }
                                }
                            } else {
                                compiler_bail!(&source_context, "Failed to resolve import {} within namespace {}", imported_node_name, composite_import.namespace);
                            }
                        }
                        Ok({})
                    } else {
                        Err(compiler_error!(&source_context, "Composite import {} does not refer to a namespace", composite_import.namespace))
                    }
                } else {
                    Err(compiler_error!(&source_context, "Failed to resolve composite import namespace {}", composite_import.namespace))
                }
            }
        }
    }
    fn compile_namespace_statement(scope: &Rc<CompilerLexicalScope>, statement: &NamespaceStatement, default_visibility: DeclarationVisibility) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let mut current_scope: Rc<CompilerLexicalScope> = scope.clone();

        // Allocate a new scope for the namespace and declare it
        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        for namespace_name in &statement.name.path {
            current_scope = current_scope.declare_scope(namespace_name, CompilerLexicalScopeClass::Namespace, visibility, &source_context.line_context)?;
        }
        statement.declarations.iter().map(|namespace_declaration| {
            match namespace_declaration {
                TopLevelDeclaration::EmptyStatement => { Ok({}) }
                TopLevelDeclaration::ImportStatement(import_statement) => { Self::compile_import_statement(&current_scope, import_statement) }
                TopLevelDeclaration::InputStatement(input_statement) => { Self::compile_input_statement(&current_scope, input_statement) }
                TopLevelDeclaration::NamespaceStatement(nested_namespace) => { Self::compile_namespace_statement(&current_scope, nested_namespace, DeclarationVisibility::Public) }
                TopLevelDeclaration::DataStatement(data_statement) => { Self::pre_compile_data_statement(&current_scope, data_statement, DeclarationVisibility::Public)?; Ok({}) }
                TopLevelDeclaration::StructStatement(struct_statement) => { Self::compile_struct_statement(&current_scope, struct_statement, None, DeclarationVisibility::Public)?; Ok({}) }
                TopLevelDeclaration::EnumStatement(enum_statement) => { Self::pre_compile_enum_statement(&current_scope, enum_statement, None, DeclarationVisibility::Public)?; Ok({}) }
            }
        }).chain_compiler_result(|| compiler_error!(source_context, "Failed to compile namespace declaration"))
    }
    fn compile_input_statement(scope: &Rc<CompilerLexicalScope>, statement: &InputStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let name = statement.global_name.clone();
        CompilerFunctionBuilder::check_integral_or_bool_type_instruction_encoding(&statement.value_type, &source_context)?;

        scope.declare(&name, CompilerLexicalDeclarationClass::GlobalData(GlobalDataDeclaration{global_name: name.clone(), value_type: statement.value_type.clone()}), DeclarationVisibility::Public, &source_context.line_context)?;
        let maybe_default_value = if let Some(default_value_expression) = &statement.default_value {
            if let Expression::IntegerConstantExpression(int_constant_expr) = default_value_expression {
                Some(CompilerFunctionBuilder::coerce_integer_constant_expression(int_constant_expr, &statement.value_type, &source_context)?)
            } else if let Expression::BoolConstantExpression(bool_constant_expr) = default_value_expression {
                Some(if bool_constant_expr.bool_value { 1 } else { 0 })
            } else { compiler_bail!(&source_context, "Global data can only be initialized with an integer or bool constant expression (for time being)"); }
        } else { None };
        if let Some(module_codegen_data) = scope.module_codegen() && let Some(global_value) = maybe_default_value {
            module_codegen_data.visitor.borrow_mut().define_global(name.as_str(), global_value as u32 as u64).with_source_context(&source_context)?;
        }
        Ok({})
    }
    fn pre_compile_function_argument(source_function_scope: &Rc<CompilerLexicalScope>, source_function_closure: &RefCell<CompilerFunctionDeclaration>, template_argument: &TemplateArgument) -> CompilerResult<Rc<CompilerLexicalDeclaration>> {
        let source_context = CompilerSourceContext{file_name: source_function_scope.file_name(), line_context: template_argument.source_context.clone()};

        let default_value_reference = if let Some(argument_default_value_expression) = &template_argument.default_value {
            let argument_index = source_function_closure.borrow().reference.signature.explicit_parameters.as_ref().unwrap().len();
            let function_name = format!("{}@default_value@{}", source_function_scope.name.as_str(), argument_index);

            let function_closure = Rc::new(RefCell::new(CompilerFunctionDeclaration {
                reference: CompilerFunctionReference{
                    function: GospelSourceObjectReference::default(),
                    signature: CompilerFunctionSignature{ implicit_parameters: source_function_closure.borrow().reference.signature.implicit_parameters.clone(), ..CompilerFunctionSignature::default() },
                    return_value_type_name: None,
                },
                metadata: BTreeMap::new(),
            }));
            let function_parent_scope = source_function_scope.parent_scope().unwrap();
            let default_value_function_scope = function_parent_scope.declare_scope(function_name.as_str(), CompilerLexicalScopeClass::Function(CompilerResource{resource_handle: function_closure.clone()}), source_function_scope.visibility, &source_context.line_context)?;

            function_closure.borrow_mut().reference.function = GospelSourceObjectReference{module_name: default_value_function_scope.module_name(), local_name: default_value_function_scope.full_scope_name_no_module_name()};
            function_closure.borrow_mut().reference.signature.return_value_type = template_argument.value_type.clone();
            function_closure.borrow_mut().reference.signature.implicit_parameters = source_function_closure.borrow().reference.signature.implicit_parameters.clone();
            function_closure.borrow_mut().reference.signature.explicit_parameters = source_function_closure.borrow().reference.signature.explicit_parameters.clone();

            if let Some(module_codegen_data) = default_value_function_scope.module_codegen() {
                module_codegen_data.push_delayed_function_definition(&default_value_function_scope, Box::new(CompilerSimpleExpressionFunctionGenerator{
                    source_context: default_value_function_scope.source_context.line_context.clone(),
                    return_value_expression: argument_default_value_expression.clone(),
                }))?;
            }
            Some(function_closure.borrow().reference.clone())
        } else { None };

        let new_parameter_declaration = source_function_scope.declare(template_argument.name.as_str(),
          CompilerLexicalDeclarationClass::Parameter(template_argument.value_type.clone()), DeclarationVisibility::Private, &source_context.line_context)?;

        source_function_closure.borrow_mut().reference.signature.explicit_parameters.as_mut().unwrap().push(CompilerFunctionParameter{
            parameter_type: template_argument.value_type.clone(),
            default_value: default_value_reference,
            parameter_declaration: Rc::downgrade(&new_parameter_declaration),
        });
        Ok(new_parameter_declaration)
    }
    fn declare_function(scope: &Rc<CompilerLexicalScope>, function_name: &str, visibility: DeclarationVisibility, return_value_type: ExpressionValueType, template_declaration: Option<&TemplateDeclaration>, is_type_definition: bool, source_context: &ASTSourceContext) -> CompilerResult<(Rc<CompilerLexicalScope>, Rc<RefCell<CompilerFunctionDeclaration>>)> {
        let actual_source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: source_context.clone()};

        let implicit_parameters = scope.collect_implicit_scope_parameters();
        let function_closure = Rc::new(RefCell::new(CompilerFunctionDeclaration {
            reference: CompilerFunctionReference{
                function: GospelSourceObjectReference::default(),
                signature: CompilerFunctionSignature{ return_value_type: return_value_type.clone(), implicit_parameters, explicit_parameters: None },
                return_value_type_name: None,
            },
            metadata: BTreeMap::new(),
        }));
        let function_scope = scope.declare_scope(function_name, CompilerLexicalScopeClass::Function(CompilerResource{resource_handle: function_closure.clone()}), visibility, &actual_source_context.line_context)?;
        function_closure.borrow_mut().reference.function = GospelSourceObjectReference{module_name: scope.module_name(), local_name: function_scope.full_scope_name_no_module_name()};
        if return_value_type == ExpressionValueType::Typename && is_type_definition {
            function_closure.borrow_mut().reference.return_value_type_name = Some(function_scope.full_scope_name());
        }

        if let Some(template_arguments) = template_declaration {
            function_closure.borrow_mut().reference.signature.explicit_parameters = Some(Vec::new());
            for function_argument in &template_arguments.arguments {
                Self::pre_compile_function_argument(&function_scope, &function_closure, function_argument)?;
            }
        }
        Ok((function_scope, function_closure))
    }
    fn pre_compile_data_statement(scope: &Rc<CompilerLexicalScope>, statement: &DataStatement, default_visibility: DeclarationVisibility) -> CompilerResult<CompilerFunctionReference> {
        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        let (function_scope, function_closure) = Self::declare_function(scope, statement.name.as_str(), visibility,
            statement.value_type.clone(), statement.template_declaration.as_ref(), false, &statement.source_context)?;

        if let Some(doc_comment) = &statement.doc_comment {
            function_closure.borrow_mut().metadata.insert(String::from("doc"), doc_comment.clone());
        }
        if let Some(module_codegen_data) = function_scope.module_codegen() {
            module_codegen_data.push_delayed_function_definition(&function_scope, Box::new(CompilerSimpleExpressionFunctionGenerator{
                source_context: statement.source_context.clone(),
                return_value_expression: statement.initializer.clone(),
            }))?;
        }
        Ok(function_closure.borrow().reference.clone())
    }
    fn pre_compile_enum_statement(scope: &Rc<CompilerLexicalScope>, statement: &EnumStatement, fallback_name: Option<&str>, default_visibility: DeclarationVisibility) -> CompilerResult<CompilerFunctionReference> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let function_name = statement.name.as_ref().map(|x| x.as_str()).or(fallback_name)
            .ok_or_else(|| compiler_error!(&source_context, "Unnamed enum declaration in top level scope. All top level enumerations must have a name"))?;

        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        let (function_scope, function_closure) = Self::declare_function(scope, function_name, visibility,
            ExpressionValueType::Typename, statement.template_declaration.as_ref(), true, &source_context.line_context)?;

        let mut constant_doc_comment_lookup: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for constant in &statement.constants {
            if let Some(constant_name) = &constant.name && let Some(constant_doc_comment) = &constant.doc_comment {
                constant_doc_comment_lookup.entry(constant_name.clone()).or_default().push(constant_doc_comment.clone());
            }
        }
        if let Some(doc_comment) = &statement.doc_comment {
            function_closure.borrow_mut().metadata.insert(String::from("doc"), doc_comment.clone());
        }
       for (constant_name, constant_doc_list) in constant_doc_comment_lookup {
            let constant_doc = constant_doc_list.join("\n");
            function_closure.borrow_mut().metadata.insert(format!("doc_{}", constant_name), constant_doc);
        }

        let (allow_partial_types, generate_prototype_layouts) = scope.compiler().map(|x| (x.compiler_options.allow_partial_types, x.compiler_options.generate_prototype_layouts)).unwrap_or((false, false));
        if let Some(module_codegen_data) = scope.module_codegen() {
            module_codegen_data.push_delayed_function_definition(&function_scope, Box::new(CompilerEnumFunctionGenerator{
                source_context,
                enum_kind: statement.enum_kind,
                underlying_type_expression: statement.underlying_type_expression.clone(),
                allow_partial_types, generate_prototype_layout: generate_prototype_layouts,
                constants: statement.constants.clone(),
            }))?;
        }
        Ok(function_closure.borrow().reference.clone())
    }
    fn pre_compile_type_layout_block_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &BlockDeclaration) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let block_scope = scope.declare_scope_generated_name("block", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: block_declaration.clone()}), &source_context.line_context)?;

        let fragments = declaration.declarations.iter().map(|declaration| {
            Self::pre_compile_type_layout_inner_declaration(&block_scope, declaration, None)
        }).collect_compiler_result(|| compiler_error!(&source_context, "Failed to pre-compile block declaration"))?;

        Ok(Box::new(CompilerStructBlockFragment{block_declaration, fragments}))
    }
    fn pre_compile_type_layout_conditional_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &ConditionalDeclaration) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};

        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
        let then_scope = scope.declare_scope_generated_name("then", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: then_block_declaration.clone()}), &declaration.source_context)?;
        let then_fragment = Self::pre_compile_type_layout_inner_declaration(&then_scope, &declaration.then_branch, None)?;

        let else_branch = if let Some(else_statement) = &declaration.else_branch {
            let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{block_range: CompilerInstructionRange::default(), loop_codegen_data: None}));
            let else_scope = scope.declare_scope_generated_name("else", CompilerLexicalScopeClass::Block(CompilerResource{resource_handle: else_block_declaration.clone()}), &declaration.source_context)?;
            let else_fragment = Self::pre_compile_type_layout_inner_declaration(&else_scope, &else_statement, None)?;
            Some((else_block_declaration, else_fragment))
        } else { None };

        Ok(Box::new(CompilerStructConditionalFragment{
            source_context,
            scope: scope.clone(), condition_expression: declaration.condition_expression.clone(),
            then_block_declaration, then_fragment, else_branch
        }))
    }
    fn pre_compile_type_layout_struct_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &StructStatement, visibility_override: Option<DeclarationVisibility>) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        let visibility = visibility_override.unwrap_or(scope.visibility);
        let struct_reference = CompilerInstance::compile_struct_statement(scope, &declaration, None, visibility)?;

        let metadata_field_name = declaration.name.as_ref().ok_or_else(|| compiler_error!(&source_context, "Unnamed struct declaration in top level scope. All top level structs must have a name"))?;
        Ok(Box::new(CompilerStructMetadataFragment{
            source_context,
            scope: scope.clone(),
            metadata_function_reference: struct_reference,
            metadata_name: metadata_field_name.clone()
        }))
    }
    fn pre_compile_type_layout_data_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &DataStatement, visibility_override: Option<DeclarationVisibility>) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        let visibility = visibility_override.unwrap_or(scope.visibility);
        let data_reference = CompilerInstance::pre_compile_data_statement(scope, &declaration, visibility)?;

        let metadata_field_name = declaration.name.clone();
        Ok(Box::new(CompilerStructMetadataFragment{
            source_context,
            scope: scope.clone(),
            metadata_function_reference: data_reference,
            metadata_name: metadata_field_name.clone()
        }))
    }
    fn pre_compile_type_layout_member_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &MemberDeclaration) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        Ok(Box::new(CompilerStructMemberFragment{
            source_context,
            scope: scope.clone(),
            member_name: declaration.name.clone(),
            member_type_expression: declaration.member_type_expression.clone(),
            alignment_expression: declaration.alignment_expression.clone(),
            array_size_expression: declaration.array_size_expression.clone(),
            bitfield_width_expression: declaration.bitfield_width_expression.clone(),
        }))
    }
    fn pre_compile_type_layout_function_declaration(scope: &Rc<CompilerLexicalScope>, declaration: &MemberFunctionDeclaration) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        Ok(Box::new(CompilerStructVirtualFunctionFragment{
            source_context,
            scope: scope.clone(),
            function_name: declaration.name.clone(),
            return_type_expression: declaration.return_value_type.clone(),
            parameters: declaration.parameters.clone(),
            constant: declaration.constant,
            is_override: declaration.is_override,
        }))
    }
    fn pre_compile_type_layout_inner_declaration(scope: &Rc<CompilerLexicalScope>, inner_declaration: &StructInnerDeclaration, visibility_override: Option<DeclarationVisibility>) -> CompilerResult<Box<dyn CompilerStructFragmentGenerator>> {
        match inner_declaration {
            StructInnerDeclaration::BlockDeclaration(block_declaration) => {
                Self::pre_compile_type_layout_block_declaration(scope, &*block_declaration)
            }
            StructInnerDeclaration::ConditionalDeclaration(conditional_declaration) => {
                Self::pre_compile_type_layout_conditional_declaration(scope, &*conditional_declaration)
            }
            StructInnerDeclaration::NestedStructDeclaration(struct_declaration) => {
                Self::pre_compile_type_layout_struct_declaration(scope, &*struct_declaration, visibility_override)
            }
            StructInnerDeclaration::DataDeclaration(data_declaration) => {
                Self::pre_compile_type_layout_data_declaration(scope, &*data_declaration, visibility_override)
            }
            StructInnerDeclaration::MemberDeclaration(member_declaration) => {
                Self::pre_compile_type_layout_member_declaration(scope, &*member_declaration)
            }
            StructInnerDeclaration::FunctionDeclaration(function_declaration) => {
                Self::pre_compile_type_layout_function_declaration(scope, &*function_declaration)
            }
            StructInnerDeclaration::EmptyDeclaration => {
                Ok(Box::new(BlankStructFragmentGenerator{}))
            }
        }
    }
    fn compile_struct_statement(scope: &Rc<CompilerLexicalScope>, statement: &StructStatement, fallback_name: Option<&str>, default_visibility: DeclarationVisibility) -> CompilerResult<CompilerFunctionReference> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let function_name = statement.name.as_ref().map(|x| x.as_str()).or(fallback_name)
            .ok_or_else(|| compiler_error!(&source_context, "Unnamed struct declaration in top level scope. All top level structs must have a name"))?;

        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        let (function_scope, function_closure) = Self::declare_function(scope, function_name, visibility,
            ExpressionValueType::Typename, statement.template_declaration.as_ref(), true, &source_context.line_context)?;
        let visibility_override = if !function_closure.borrow().reference.signature.implicit_parameters.is_empty() || function_closure.borrow().reference.signature.explicit_parameters.is_some() {
            Some(DeclarationVisibility::Private)
        } else { None };

        let mut member_doc_comment_lookup: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for declaration in statement.declarations.iter().flat_map(|x| x.iterate_recursive()) {
            if let StructInnerDeclaration::MemberDeclaration(member) = declaration && 
                let Some(constant_name) = &member.name && 
                let Some(constant_doc_comment) = &member.doc_comment {
                member_doc_comment_lookup.entry(constant_name.clone()).or_default().push(constant_doc_comment.clone());
            }
        }
        if let Some(doc_comment) = &statement.doc_comment {
            function_closure.borrow_mut().metadata.insert(String::from("doc"), doc_comment.clone());
        }
        for (constant_name, constant_doc_list) in member_doc_comment_lookup {
            let constant_doc = constant_doc_list.join("\n");
            function_closure.borrow_mut().metadata.insert(format!("doc_{}", constant_name), constant_doc);
        };

        let fragments = statement.declarations.iter().map(|struct_inner_declaration| {
            Self::pre_compile_type_layout_inner_declaration(&function_scope, struct_inner_declaration, visibility_override)
        }).collect_compiler_result(|| compiler_error!(&source_context, "Failed to pre-compile struct definition"))?;

        let (allow_partial_types, generate_prototype_layouts) = scope.compiler().map(|x| (x.compiler_options.allow_partial_types, x.compiler_options.generate_prototype_layouts)).unwrap_or((false, false));
        if let Some(module_codegen_data) = scope.module_codegen() {
            module_codegen_data.push_delayed_function_definition(&function_scope, Box::new(CompilerStructFunctionGenerator{
                source_context,
                struct_kind: statement.struct_kind,
                alignment_expression: statement.alignment_expression.clone(),
                member_pack_alignment_expression: statement.member_pack_expression.clone(),
                base_class_expressions: statement.base_class_expressions.clone(),
                allow_partial_types, generate_prototype_layout: generate_prototype_layouts,
                fragments,
            }))?;
        }
        Ok(function_closure.borrow().reference.clone())
    }
}

/// Represents a compiler resource that can be read from the outside but not modified
#[derive(Debug, Clone)]
pub struct CompilerResource<T> {
    resource_handle: Rc<RefCell<T>>,
}
impl<T> CompilerResource<T> {
    fn borrow_mut(&self) -> RefMut<'_, T> {
        self.resource_handle.borrow_mut()
    }
    pub fn borrow(&self) -> Ref<'_, T> {
        self.resource_handle.borrow()
    }
}

/// Represents a local variable declaration in source code
#[derive(Debug, Clone)]
pub struct CompilerLocalVariableDeclaration {
    pub value_slot: u32,
    pub variable_type: ExpressionValueType,
}

/// Represents a global data (input variable) declaration in source code
#[derive(Debug, Clone)]
pub struct GlobalDataDeclaration {
    pub global_name: String,
    pub value_type: ExpressionValueType,
}

/// Describes possible kinds of declarations in the compiler
#[derive(Debug, Clone, Display)]
pub enum CompilerLexicalDeclarationClass {
    /// Represents a global data declaration (input variable)
    #[strum(to_string = "global data")]
    GlobalData(GlobalDataDeclaration),
    /// Represents a function parameter (template argument). Value is a parameter type
    #[strum(to_string = "parameter")]
    Parameter(ExpressionValueType),
    /// Represents an import statement
    #[strum(to_string = "import")]
    Import(Weak<CompilerLexicalDeclaration>),
    /// Represents a namespace import
    #[strum(to_string = "namespace import")]
    NamespaceImport(Weak<CompilerLexicalScope>),
    /// Represents a local variable declaration
    #[strum(to_string = "local variable")]
    LocalVariable(CompilerLocalVariableDeclaration),
}

/// Describes a visibility of a declaration relative to other declarations
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum DeclarationVisibility {
    Public,
    ModuleInternal,
    FileLocal,
    Private,
}
impl DeclarationVisibility {
    /// Between two visibilities, returns the one that is more private
    pub fn intersect(self, other: Self) -> Self {
        if self > other { self } else { other }
    }
}
#[derive(Debug, Clone)]
struct DeclarationVisibilityContext {
    module_name: Option<String>,
    file_name: Option<String>,
    source_scope: Option<Rc<CompilerLexicalScope>>,
}

/// Represents a declaration within the scope
#[derive(Debug, Clone)]
pub struct CompilerLexicalDeclaration {
    parent: Weak<CompilerLexicalScope>,
    pub class: CompilerLexicalDeclarationClass,
    pub name: String,
    pub visibility: DeclarationVisibility,
    pub source_context: CompilerSourceContext,
}
impl Display for CompilerLexicalDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} ({})", self.class, self.full_declaration_display_name(), self.source_context)
    }
}
impl CompilerLexicalDeclaration {
    /// Returns the parent scope of this declaration
    pub fn parent_scope(self: &Rc<Self>) -> Option<Rc<CompilerLexicalScope>> {
        self.parent.upgrade()
    }
    /// Returns full mangled name of this declaration (:: replaced with $). Excludes the module name
    pub fn full_declaration_name_no_module_name(&self) -> String {
        let scope_full_name = self.parent.upgrade().map(|x| x.full_scope_name_no_module_name()).unwrap_or(String::from("<unknown>"));
        format!("{}${}", scope_full_name, self.name.as_str())
    }
    /// Returns full mangled name of this declaration (:: replaced with $)
    pub fn full_declaration_name(&self) -> String {
        let scope_full_name = self.parent.upgrade().map(|x| x.full_scope_name()).unwrap_or(String::from("<unknown>"));
        format!("{}${}", scope_full_name, self.name.as_str())
    }
    /// Returns the full display name for the declaration (:: as a separator)
    pub fn full_declaration_display_name(&self) -> String {
        let scope_full_name = self.parent.upgrade().map(|x| x.full_scope_display_name()).unwrap_or(String::from("<unknown>"));
        format!("{}::{}", scope_full_name, self.name)
    }
}

#[derive(Debug, Clone, Default)]
struct CompilerLoopCodegenData {
    loop_start_fixups: Vec<GospelJumpLabelFixup>,
    loop_finish_fixups: Vec<GospelJumpLabelFixup>,
}

/// Represents an instruction range describing the location of the source level object within the compiled code
#[derive(Debug, Clone, Default)]
pub struct CompilerInstructionRange {
    pub start_instruction_index: u32,
    pub end_instruction_index: u32,
}

/// Represents a block declaration within the function
#[derive(Debug, Clone)]
pub struct CompilerBlockDeclaration {
    pub block_range: CompilerInstructionRange,
    loop_codegen_data: Option<CompilerLoopCodegenData>,
}

/// Represents a function declaration
#[derive(Debug, Clone)]
pub struct CompilerFunctionDeclaration {
    pub reference: CompilerFunctionReference,
    pub metadata: BTreeMap<String, String>,
}

trait CompilerFunctionCodeGenerator : Debug {
    fn generate(&self, function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<()>;
}

#[derive(Debug)]
struct CompilerDelayedImportResolutionData {
    scope: Rc<CompilerLexicalScope>,
    statement: ImportStatement,
}
#[derive(Debug)]
struct CompilerFunctionCodegenData {
    function_scope: Rc<CompilerLexicalScope>,
    function_generator: Box<dyn CompilerFunctionCodeGenerator>,
}

#[derive(Debug)]
struct CompilerModuleCodegenData {
    visitor: Rc<RefCell<dyn GospelModuleVisitor>>,
    imports: RefCell<Vec<Option<CompilerDelayedImportResolutionData>>>,
    functions: RefCell<Vec<Option<CompilerFunctionCodegenData>>>,
}
impl CompilerModuleCodegenData {
    fn push_delayed_import(&self, scope: &Rc<CompilerLexicalScope>, statement: &ImportStatement) -> CompilerResult<()> {
        self.imports.borrow_mut().push(Some(CompilerDelayedImportResolutionData{
            scope: scope.clone(), statement: statement.clone()
        }));
        Ok({})
    }
    fn push_delayed_function_definition(&self, function_scope: &Rc<CompilerLexicalScope>, generator: Box<dyn CompilerFunctionCodeGenerator>) -> CompilerResult<()> {
        // Declare the function immediately so future function definitions can refer to it
        let (function_declaration, _, _, _) = CompilerFunctionBuilder::pre_compile_function(function_scope)?;
        self.visitor.borrow_mut().declare_function(function_declaration).with_source_context(&function_scope.source_context)?;

        // Push the delayed function definition now
        self.functions.borrow_mut().push(Some(CompilerFunctionCodegenData{function_scope: function_scope.clone(), function_generator: generator}));
        Ok({})
    }
    fn compile_import_statements(&self, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        let mut current_import_index: usize = 0;
        while current_import_index < self.imports.borrow().len() {
            let import_statement = std::mem::take(&mut self.imports.borrow_mut()[current_import_index])
                .ok_or_else(|| compiler_error!(source_context, "Internal compiler error: Attempting to process import already moved out"))?;
            current_import_index += 1;
            CompilerInstance::compile_import_statement(&import_statement.scope, &import_statement.statement)?;
        }
        self.imports.borrow_mut().clear();
        Ok({})
    }
    fn compile_function_definitions(&self, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        let mut current_function_index: usize = 0;
        while current_function_index < self.functions.borrow().len() {
            let function_definition = std::mem::take(&mut self.functions.borrow_mut()[current_function_index])
                .ok_or_else(|| compiler_error!(source_context, "Internal compiler error: Attempting to process function already moved out"))?;
            current_function_index += 1;
            function_definition.function_generator.generate(&function_definition.function_scope)?;
        }
        self.functions.borrow_mut().clear();
        Ok({})
    }
}

/// Describes a module-level compiler metadata. This should not be used outside the compiler, use functions of CompilerLexicalScope instead
#[derive(Debug, Clone)]
pub struct CompilerModuleData {
    compiler: Weak<CompilerInstance>,
    codegen_data: RefCell<Option<Rc<CompilerModuleCodegenData>>>,
}

/// Describes a source file-level compiler metadata
#[derive(Debug, Clone)]
pub struct CompilerSourceFileData {
    /// Name of this source file, including extension
    pub file_name: String,
}

/// Describes a type of the scope. Different scope types describe different source level objects and contain different metadata
#[derive(Debug, Clone, Display)]
pub enum CompilerLexicalScopeClass {
    /// Represents a top level module scope
    #[strum(to_string = "module")]
    Module(CompilerModuleData),
    /// Represents a source file scope within the module
    #[strum(to_string = "source file")]
    SourceFile(CompilerSourceFileData),
    /// Represents a namespace (declared with namespace statement)
    #[strum(to_string = "namespace")]
    Namespace,
    /// Represents a function declaration (represents type alias or type declaration)
    #[strum(to_string = "function")]
    Function(CompilerResource<CompilerFunctionDeclaration>),
    /// Represents a logical block within the function
    #[strum(to_string = "block")]
    Block(CompilerResource<CompilerBlockDeclaration>),
}

/// Lexical node refers to either a child scope or a declaration within the parent scope
#[derive(Debug, Clone, Display)]
pub enum CompilerLexicalNode {
    #[strum(to_string = "{0} scope")]
    Scope(Rc<CompilerLexicalScope>),
    #[strum(to_string = "{0} declaration")]
    Declaration(Rc<CompilerLexicalDeclaration>)
}
impl PartialEq for CompilerLexicalNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (CompilerLexicalNode::Scope(self_scope), CompilerLexicalNode::Scope(other_scope)) => Rc::ptr_eq(self_scope, other_scope),
            (CompilerLexicalNode::Declaration(self_decl), CompilerLexicalNode::Declaration(other_decl)) => Rc::ptr_eq(self_decl, other_decl),
            _ => false,
        }
    }
}
impl Eq for CompilerLexicalNode {}
impl CompilerLexicalNode {
    /// Returns the name of this lexical node
    pub fn node_name(&self) -> &str {
        match &self {
            CompilerLexicalNode::Scope(scope) => scope.name.as_str(),
            CompilerLexicalNode::Declaration(decl) => decl.name.as_str(),
        }
    }
    /// Returns the parent scope of this lexical node
    fn node_parent(&self) -> Option<Rc<CompilerLexicalScope>> {
        match &self {
            CompilerLexicalNode::Scope(scope) => scope.parent.as_ref().and_then(|x| x.upgrade()),
            CompilerLexicalNode::Declaration(decl) => decl.parent.upgrade(),
        }
    }
    fn is_visible_from(&self, visibility_context: &DeclarationVisibilityContext) -> bool {
        if let Some(parent_scope) = self.node_parent() {
            match &self {
                CompilerLexicalNode::Scope(scope) => { parent_scope.is_declaration_visible(scope.visibility, visibility_context) }
                CompilerLexicalNode::Declaration(decl) => { parent_scope.is_declaration_visible(decl.visibility, visibility_context) }
            }
        } else {
            match &self {
                CompilerLexicalNode::Scope(scope) => { scope.is_declaration_visible(scope.visibility, visibility_context) }
                CompilerLexicalNode::Declaration(_) => { false }
            }
        }
    }
}

/// Lexical scope represents a scope within which other nodes (scope or terminal) can be defined
#[derive(Debug)]
pub struct CompilerLexicalScope {
    parent: Option<Weak<CompilerLexicalScope>>,
    pub class: CompilerLexicalScopeClass,
    pub name: String,
    pub visibility: DeclarationVisibility,
    pub source_context: CompilerSourceContext,
    children: RefCell<Vec<CompilerLexicalNode>>,
    child_lookup: RefCell<HashMap<String, CompilerLexicalNode>>,
    unique_name_counter: RefCell<usize>,
}
impl Display for CompilerLexicalScope {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let scope_full_name = self.parent.as_ref()
            .and_then(|x| x.upgrade())
            .map(|x| format!("{}::{}", x.full_scope_display_name(), self.name.as_str()))
            .unwrap_or(self.name.clone());
        write!(f, "{} {} ({})", self.class, scope_full_name, self.source_context)
    }
}
impl CompilerLexicalScope {
    fn create_module_scope(compiler: &Rc<CompilerInstance>, module_name: String, source_context: &CompilerSourceContext, codegen_visitor: Option<Rc<RefCell<dyn GospelModuleVisitor>>>) -> Rc<Self> {
        let maybe_codegen_data = codegen_visitor.map(|x| Rc::new(CompilerModuleCodegenData{
            visitor: x, imports: RefCell::new(Vec::new()), functions: RefCell::new(Vec::new())
        }));
        Rc::new(Self{
            parent: None,
            class: CompilerLexicalScopeClass::Module(CompilerModuleData{compiler: Rc::downgrade(compiler), codegen_data: RefCell::new(maybe_codegen_data)}),
            name: module_name,
            visibility: DeclarationVisibility::Public,
            source_context: source_context.clone(),
            children: RefCell::new(Vec::new()),
            child_lookup: RefCell::new(HashMap::new()),
            unique_name_counter: RefCell::new(0),
        })
    }
    fn declare_scope_internal(self: &Rc<Self>, name: &str, class: CompilerLexicalScopeClass, visibility: DeclarationVisibility, source_context: &ASTSourceContext) -> CompilerResult<Rc<CompilerLexicalScope>> {
        let file_name_override = if let CompilerLexicalScopeClass::SourceFile(file_name) = &class { Some(file_name.file_name.clone()) } else { None };
        let new_scope = Rc::new(Self{
            parent: Some(Rc::downgrade(self)),
            class,
            name: name.to_string(),
            visibility: self.visibility.intersect(visibility),
            source_context: CompilerSourceContext{file_name: file_name_override.or(self.source_context.file_name.clone()), line_context: source_context.clone()},
            children: RefCell::new(Vec::new()),
            child_lookup: RefCell::new(HashMap::new()),
            unique_name_counter: RefCell::new(0),
        });
        self.children.borrow_mut().push(CompilerLexicalNode::Scope(new_scope.clone()));
        self.child_lookup.borrow_mut().insert(name.to_string(), CompilerLexicalNode::Scope(new_scope.clone()));
        Ok(new_scope)
    }
    fn declare_scope_generated_name(self: &Rc<Self>, base_name: &str, class: CompilerLexicalScopeClass, source_context: &ASTSourceContext) -> CompilerResult<Rc<CompilerLexicalScope>> {
        let mut scope_name: String;
        loop {
            scope_name = format!("{}@gen@{}", base_name, self.unique_name_counter.borrow());
            *self.unique_name_counter.borrow_mut() += 1;
            if !self.child_lookup.borrow().contains_key(scope_name.as_str()) {
                break;
            }
        }
        self.declare_scope_internal(scope_name.as_str(), class, DeclarationVisibility::Private, source_context)
    }
    fn declare_scope(self: &Rc<Self>, name: &str, class: CompilerLexicalScopeClass, visibility: DeclarationVisibility, source_context: &ASTSourceContext) -> CompilerResult<Rc<CompilerLexicalScope>> {
        if let Some(existing_node) = self.child_lookup.borrow().get(name) {
            let actual_source_context = CompilerSourceContext{file_name: self.file_name(), line_context: source_context.clone()};
            compiler_bail!(&actual_source_context, "{} has already been declared as {} in scope {}", name, existing_node, self.full_scope_display_name());
        }
        self.declare_scope_internal(name, class, visibility, source_context)
    }
    fn declare(self: &Rc<Self>, name: &str, class: CompilerLexicalDeclarationClass, visibility: DeclarationVisibility, source_context: &ASTSourceContext) -> CompilerResult<Rc<CompilerLexicalDeclaration>> {
        if let Some(existing_node) = self.child_lookup.borrow().get(name) {
            let actual_source_context = CompilerSourceContext{file_name: self.file_name(), line_context: source_context.clone()};
            compiler_bail!(&actual_source_context, "{} has already been declared as {} in scope {}", name, existing_node, self.full_scope_display_name());
        }
        let new_declaration = Rc::new(CompilerLexicalDeclaration{
            parent: Rc::downgrade(self),
            class,
            name: name.to_string(),
            visibility: self.visibility.intersect(visibility),
            source_context: CompilerSourceContext{file_name: self.file_name(), line_context: source_context.clone()},
        });
        self.children.borrow_mut().push(CompilerLexicalNode::Declaration(new_declaration.clone()));
        self.child_lookup.borrow_mut().insert(name.to_string(), CompilerLexicalNode::Declaration(new_declaration.clone()));
        Ok(new_declaration)
    }
    /// Returns the parent scope of this scope. Returns None if this is a top level module scope
    pub fn parent_scope(self: &Rc<Self>) -> Option<Rc<Self>> {
        self.parent.as_ref().and_then(|x| x.upgrade())
    }
    /// Iterates this scope outer chain. Innermost scopes (closest to this one) appear first in the list
    pub fn iterate_scope_chain_inner_first(self: &Rc<Self>) -> impl DoubleEndedIterator<Item = Rc<Self>> {
        let mut chain_segments: Vec<Rc<Self>> = Vec::with_capacity(10);
        let mut current_scope = self.clone();
        loop {
            chain_segments.push(current_scope.clone());
            let parent_scope = current_scope.parent.as_ref().and_then(|x| x.upgrade());
            if parent_scope.is_none() {
                break;
            }
            current_scope = parent_scope.unwrap();
        }
        chain_segments.into_iter()
    }
    /// Iterates this scope outer chain. Outermost scopes (closest to the root scope) appear first in the list
    pub fn iterate_scope_chain_outer_first(self: &Rc<Self>) -> impl Iterator<Item = Rc<Self>> {
        self.iterate_scope_chain_inner_first().rev()
    }
    /// Returns iterator over the children of this scope (not recursive)
    pub fn iterate_children(self: &Rc<Self>) -> impl Iterator<Item = CompilerLexicalNode> {
        self.children.borrow().clone().into_iter()
    }
    /// Returns the name of the module with which this scope is associated
    pub fn module_name(self: &Rc<Self>) -> String {
        self.iterate_scope_chain_outer_first()
            .find(|x| matches!(x.class, CompilerLexicalScopeClass::Module(_)))
            .map(|x| x.name.clone()).unwrap()
    }
    fn module_codegen(self: &Rc<Self>) -> Option<Rc<CompilerModuleCodegenData>> {
        self.iterate_scope_chain_outer_first()
            .find_map(|x| if let CompilerLexicalScopeClass::Module(module) = &x.class { module.codegen_data.borrow().clone() } else { None })
    }
    /// Returns the compiler instance owning this lexical scope. This should always be valid under normal conditions, but scopes do not hold strong reference to the owner compiler
    pub fn compiler(self: &Rc<Self>) -> Option<Rc<CompilerInstance>> {
        self.iterate_scope_chain_outer_first()
            .find_map(|x| if let CompilerLexicalScopeClass::Module(module) = &x.class { module.compiler.upgrade() } else { None })
    }
    /// Returns name of the source code file this scope has been created from (if available)
    pub fn file_name(self: &Rc<Self>) -> Option<String> {
        self.source_context.file_name.clone()
    }
    /// Returns true if this scope is a sub-scope of the given parent scope
    pub fn is_child_of(self: &Rc<Self>, parent: &Rc<Self>) -> bool {
        let mut current_scope = Some(self.clone());
        while current_scope.is_some() && !Rc::ptr_eq(current_scope.as_ref().unwrap(), parent) {
            current_scope = current_scope.as_ref()
                .and_then(|x| x.parent.as_ref())
                .and_then(|x| x.upgrade());
        }
        current_scope.is_some()
    }
    /// Returns the full mangled (:: replaced with $) name of this scope. Excludes the name of the module
    pub fn full_scope_name_no_module_name(self: &Rc<Self>) -> String {
        self.iterate_scope_chain_outer_first().skip(1).map(|x| x.name.clone()).join("$")
    }
    /// Returns the full mangled (:: replaced with $) name of this scope
    pub fn full_scope_name(self: &Rc<Self>) -> String {
        let scope_name_chain: Vec<String> = self.iterate_scope_chain_outer_first().map(|x| x.name.clone()).collect();
        if scope_name_chain.len() == 1 {
            scope_name_chain[0].clone()
        } else {
            let module_relative_name = scope_name_chain.iter().skip(1).join("$");
            format!("{}:{}", scope_name_chain[0], module_relative_name)
        }
    }
    /// Returns the full user-facing display name (with :: as a separator) of this scope. Includes the module name
    fn full_scope_display_name(self: &Rc<Self>) -> String {
        self.iterate_scope_chain_outer_first().map(|x| x.name.clone()).join("::")
    }
    fn visibility_context(self: &Rc<Self>) -> DeclarationVisibilityContext {
        DeclarationVisibilityContext{module_name: Some(self.module_name()), file_name: self.file_name(), source_scope: Some(self.clone())}
    }
    fn is_declaration_visible(self: &Rc<Self>, visibility: DeclarationVisibility, visibility_context: &DeclarationVisibilityContext) -> bool {
        match visibility {
            DeclarationVisibility::Public => true,
            DeclarationVisibility::ModuleInternal => Some(self.module_name()) == visibility_context.module_name,
            DeclarationVisibility::FileLocal => Some(self.module_name()) == visibility_context.module_name && self.file_name() == visibility_context.file_name,
            DeclarationVisibility::Private => visibility_context.source_scope.as_ref().map(|x| x.is_child_of(self)).unwrap_or(false),
        }
    }
    /// Attempts to find a child node by its name. Returns child node if found, or None otherwise
    pub fn find_unique_child(self: &Rc<Self>, name: &str) -> Option<CompilerLexicalNode> {
        self.child_lookup.borrow().get(name).cloned()
    }
    fn find_unique_child_check_access(self: &Rc<Self>, name: &str, visibility_context: Option<&DeclarationVisibilityContext>) -> Option<CompilerLexicalNode> {
        if let Some(found_child) = self.find_unique_child(name) {
            if visibility_context.is_none() || found_child.is_visible_from(visibility_context.unwrap()) {
                Some(found_child)
            } else { None }
        } else { None }
    }
    fn resolve_relative_identifier(self: &Rc<Self>, identifier: &PartialIdentifier, visibility_context: Option<&DeclarationVisibilityContext>, mut follow_imports: bool) -> Option<CompilerLexicalNode> {
        let mut current_scope = self.clone();
        for i in 0..(identifier.path.len() - 1) {
            let child_node_name = identifier.path[i].as_str();
            let child_node = self.find_unique_child_check_access(child_node_name, visibility_context);
            current_scope = if let Some(CompilerLexicalNode::Scope(child_scope)) = child_node {
                Some(child_scope)
            } else if follow_imports &&
                let Some(CompilerLexicalNode::Declaration(child_decl)) = child_node &&
                let CompilerLexicalDeclarationClass::NamespaceImport(imported_scope) = &child_decl.class {
                follow_imports = false;
                imported_scope.upgrade()
            } else { None }?;
        }
        if let Some(child_name) = identifier.path.last() && let Some(child) = current_scope.find_unique_child_check_access(child_name.as_str(), visibility_context) {
            if follow_imports &&
                let CompilerLexicalNode::Declaration(child_decl) = &child &&
                let CompilerLexicalDeclarationClass::Import(imported_decl) = &child_decl.class {
                imported_decl.upgrade().map(|x| CompilerLexicalNode::Declaration(x))
            } else if follow_imports &&
                let CompilerLexicalNode::Declaration(child_decl) = &child &&
                let CompilerLexicalDeclarationClass::NamespaceImport(imported_scope) = &child_decl.class {
                imported_scope.upgrade().map(|x| CompilerLexicalNode::Scope(x))
            } else { Some(child) }
        } else { None }
    }
    fn collect_implicit_scope_parameters(self: &Rc<Self>) -> Vec<Weak<CompilerLexicalDeclaration>> {
        self.iterate_scope_chain_outer_first().flat_map(|x| x.iterate_children().collect::<Vec<CompilerLexicalNode>>()).filter_map(|x| {
            if let CompilerLexicalNode::Declaration(decl) = x {
                if let CompilerLexicalDeclarationClass::Parameter(_) = &decl.class {
                    Some(Rc::downgrade(&decl))
                } else if let CompilerLexicalDeclarationClass::LocalVariable(_) = &decl.class {
                    Some(Rc::downgrade(&decl))
                } else { None }
            } else { None }
        }).collect()
    }
}


