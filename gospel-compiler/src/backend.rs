use std::cell::RefCell;
use std::collections::{HashMap};
use std::fmt::{Display, Formatter};
use std::path::PathBuf;
use std::rc::{Rc, Weak};
use anyhow::anyhow;
use itertools::Itertools;
use strum_macros::Display;
use gospel_vm::bytecode::GospelOpcode;
use gospel_vm::gospel_type::{GospelPlatformConfigProperty, GospelValueType};
use gospel_vm::writer::{GospelJumpLabelFixup, GospelModuleVisitor, GospelSourceFunctionDeclaration, GospelSourceFunctionDefinition, GospelSourceObjectReference, GospelSourceSlotBinding, GospelSourceStaticValue, GospelSourceStructDefinition, GospelSourceStructField};
use crate::ast::{ASTSourceContext, AssignmentStatement, BlockStatement, ConditionalStatement, DataStatement, Expression, ExpressionValueType, ExternStatement, DeclarationStatement, ModuleImportStatement, ModuleImportStatementType, ModuleSourceFile, ModuleTopLevelDeclaration, NamespaceLevelDeclaration, NamespaceStatement, PartialIdentifier, PartialIdentifierKind, Statement, StructStatement, TemplateArgument, TemplateDeclaration, WhileLoopStatement, BinaryOperator, SimpleStatement, IdentifierExpression, UnaryExpression, UnaryOperator, BinaryExpression, ConditionalExpression, BlockExpression, IntegerConstantExpression, ArrayIndexExpression, MemberAccessExpression, StructInnerDeclaration, BlockDeclaration, ConditionalDeclaration, MemberDeclaration, BuiltinIdentifierExpression, BuiltinIdentifier, DeclarationAccessSpecifier};

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
    #[allow(dead_code)]
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

#[derive(Debug, Clone)]
struct CompilerFunctionParameter {
    parameter_type: ExpressionValueType,
    default_value: Option<CompilerFunctionReference>,
    parameter_declaration: Weak<CompilerLexicalDeclaration>,
}

#[derive(Debug, Clone, Default)]
struct CompilerFunctionSignature {
    implicit_parameters: Vec<Weak<CompilerLexicalDeclaration>>,
    explicit_parameters: Option<Vec<CompilerFunctionParameter>>,
    return_value_type: ExpressionValueType,
}

#[derive(Debug, Clone, Default)]
struct CompilerFunctionReference {
    function: GospelSourceObjectReference,
    signature: CompilerFunctionSignature,
}

#[derive(Debug)]
pub struct CompilerInstance {
    module_scopes: RefCell<HashMap<String, Rc<CompilerLexicalScope>>>,
}

#[derive(Debug)]
struct CompilerFunctionBuilder {
    function_scope: Rc<CompilerLexicalScope>,
    function_definition: GospelSourceFunctionDefinition,
    argument_source_declarations: Vec<Rc<CompilerLexicalDeclaration>>,
    function_closure: CompilerFunctionReference,
    constant_slot_lookup: HashMap<(GospelValueType, GospelSourceSlotBinding), u32>,
    inline_struct_counter: usize,
}
impl CompilerFunctionBuilder {
    fn create(function_scope: &Rc<CompilerLexicalScope>) -> CompilerResult<CompilerFunctionBuilder> {
        let function_reference = if let CompilerLexicalScopeClass::Function(function_closure) = &function_scope.class {
            let borrowed_closure = function_closure.borrow();
            borrowed_closure.function_reference.clone()
        } else {
            compiler_bail!(&function_scope.source_context, "Internal error: expected data scope in CompilerFunctionBuilder");
        };

        let mut function_declaration: GospelSourceFunctionDeclaration = GospelSourceFunctionDeclaration::create(
            function_reference.function.clone(), function_scope.visibility != DeclarationVisibility::Public);
        function_declaration.set_return_value_type(CompilerInstance::convert_value_type(function_reference.signature.return_value_type));
        let mut argument_source_declarations: Vec<Rc<CompilerLexicalDeclaration>> = Vec::new();

        for weak_implicit_parameter in &function_reference.signature.implicit_parameters {
            if let Some(implicit_parameter) = weak_implicit_parameter.upgrade() {
                match &implicit_parameter.class {
                    CompilerLexicalDeclarationClass::Parameter(parameter_type) => {
                        function_declaration.add_function_argument(CompilerInstance::convert_value_type(parameter_type.clone())).with_source_context(&function_scope.source_context)?;
                        argument_source_declarations.push(implicit_parameter);
                    }
                    CompilerLexicalDeclarationClass::LocalVariable(local_variable) => {
                        function_declaration.add_function_argument(CompilerInstance::convert_value_type(local_variable.variable_type.clone())).with_source_context(&function_scope.source_context)?;
                        argument_source_declarations.push(implicit_parameter);
                    }
                    _ => { compiler_bail!(&function_scope.source_context, "Internal error: expected Parameter or LocalVariable declaration as implicit function parameters, got {}", implicit_parameter.class); }
                }
            } else {
                compiler_bail!(&function_scope.source_context, "Internal error: lost reference to the implicit function parameter");
            }
        }

        if let Some(explicit_function_parameters) = &function_reference.signature.explicit_parameters {
            for explicit_function_parameter in explicit_function_parameters {
                if let Some(parameter_declaration) = explicit_function_parameter.parameter_declaration.upgrade() {
                    function_declaration.add_function_argument(CompilerInstance::convert_value_type(explicit_function_parameter.parameter_type.clone())).with_source_context(&function_scope.source_context)?;
                    argument_source_declarations.push(parameter_declaration);
                } else {
                    compiler_bail!(&function_scope.source_context, "Internal error: lost reference to the explicit function parameter");
                }
            }
        }
        Ok(CompilerFunctionBuilder{
            function_scope: function_scope.clone(),
            function_definition: GospelSourceFunctionDefinition::create(function_declaration),
            argument_source_declarations,
            function_closure: function_reference,
            constant_slot_lookup: HashMap::new(),
            inline_struct_counter: 0,
        })
    }
    fn nested_declaration_visibility(&self) -> DeclarationVisibility {
        // Nested declarations in functions that have parameters or implicit lexical parameters cannot be public because they need to have these parameters bound,
        // and they can only be implicitly bound for the children of the function scope
        if !self.function_closure.signature.implicit_parameters.is_empty() || self.function_closure.signature.explicit_parameters.is_some() {
            DeclarationVisibility::Private
        } else { DeclarationVisibility::Public }
    }
    fn compile_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &Expression) -> CompilerResult<ExpressionValueType> {
        match expression {
            Expression::IdentifierExpression(identifier_expression) => { self.compile_identifier_expression(scope, &*identifier_expression) }
            Expression::UnaryExpression(unary_expression) => { self.compile_unary_expression(scope, &*unary_expression) }
            Expression::BinaryExpression(binary_expression) => { self.compile_binary_expression(scope, &*binary_expression) }
            Expression::ConditionalExpression(conditional_expression) => { self.compile_conditional_expression(scope, &*conditional_expression) }
            Expression::BlockExpression(block_expression) => { self.compile_block_expression(scope, &*block_expression) }
            Expression::IntegerConstantExpression(constant_expression) => { self.compile_integer_constant_expression(scope, &*constant_expression) }
            Expression::ArrayIndexExpression(array_index_expression) => { self.compile_array_index_expression(scope, &*array_index_expression) }
            Expression::MemberAccessExpression(member_access_expression) => { self.compile_member_access_expression(scope, &*member_access_expression) }
            Expression::StructDeclarationExpression(struct_declaration_expression) => { self.compile_struct_declaration_expression(scope, &*struct_declaration_expression) }
            Expression::BuiltinIdentifierExpression(builtin_identifier_expression) => { self.compile_builtin_identifier_expression(scope, &*builtin_identifier_expression) }
        }
    }
    fn compile_builtin_identifier_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BuiltinIdentifierExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let static_value = match expression.identifier {
            BuiltinIdentifier::AddressSize => GospelSourceStaticValue::PlatformConfigProperty(GospelPlatformConfigProperty::AddressSize),
            BuiltinIdentifier::TargetPlatform => GospelSourceStaticValue::PlatformConfigProperty(GospelPlatformConfigProperty::TargetOS),
            BuiltinIdentifier::TargetArch => GospelSourceStaticValue::PlatformConfigProperty(GospelPlatformConfigProperty::TargetArch),
        };
        let constant_slot_index = self.find_or_define_constant_slot(GospelValueType::Integer, GospelSourceSlotBinding::StaticValue(static_value), &source_context)?;
        Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, constant_slot_index).with_source_context(&source_context)?);
        Ok(ExpressionValueType::Int)
    }
    fn compile_struct_declaration_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &StructStatement) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        let struct_function_name = format!("@inline_struct@{}", self.inline_struct_counter);
        self.inline_struct_counter += 1;
        let struct_reference = CompilerInstance::compile_struct_statement(scope, expression, Some(struct_function_name.as_str()), DeclarationVisibility::Private)?;
        self.compile_static_function_call(scope, &struct_reference, &source_context, None, true)
    }
    fn emit_runtime_typecheck(&mut self, scope: &Rc<CompilerLexicalScope>, source_context: &CompilerSourceContext, expected_expression_type: ExpressionValueType) -> CompilerResult<()> {
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Dup).with_source_context(source_context)?);

        // if typeof(x) == expected_expression_type { jump to end } else { abort }
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Typeof).with_source_context(source_context)?);
        Self::attach_source_context(scope, source_context, self.function_definition.add_int_constant_instruction(CompilerInstance::convert_value_type(expected_expression_type) as i32).with_source_context(source_context)?);
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);

        let (jump_instruction_index, jump_to_end_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(source_context)?;
        Self::attach_source_context(scope, source_context, jump_instruction_index);
        Self::attach_source_context(scope, source_context, self.function_definition.add_string_instruction(GospelOpcode::Abort, format!("Runtime typecheck failed: Expected {}", expected_expression_type).as_str()).with_source_context(source_context)?);

        let end_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(source_context)?;
        Ok({})
    }
    fn compile_member_access_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &MemberAccessExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        let target_expression_type = self.compile_expression(scope, &expression.type_expression)?;
        Self::check_expression_type(&source_context, ExpressionValueType::Typename, target_expression_type)?;
        Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutGetMetadata).with_source_context(&source_context)?);

        if let Some(template_arguments) = &expression.template_arguments {
            // Member access expression is a closure call, so we need to read the value as the closure and then call it
            Self::attach_source_context(scope, &source_context, self.function_definition.add_typed_member_access_instruction(GospelOpcode::StructGetNamedTypedField, expression.member_name.as_str(), GospelValueType::Closure).with_source_context(&source_context)?);
            for function_argument_expression in template_arguments {
                self.compile_expression(scope, function_argument_expression)?;
            }
            Self::attach_source_context(scope, &source_context, self.function_definition.add_variadic_instruction(GospelOpcode::Call, template_arguments.len() as u32).with_source_context(&source_context)?);
            // Closure return value is not known compile time, so we need to emit a runtime type check
            self.emit_runtime_typecheck(scope, &source_context, expression.member_type)?;
            Ok(expression.member_type)
        } else {
            // Member access expression is just a read from the metadata struct, not a closure call. StructGetNamedTypedField will do a runtime typecheck for us
            let member_field_type = CompilerInstance::convert_value_type(expression.member_type);
            Self::attach_source_context(scope, &source_context, self.function_definition.add_typed_member_access_instruction(GospelOpcode::StructGetNamedTypedField, expression.member_name.as_str(), member_field_type).with_source_context(&source_context)?);
            Ok(expression.member_type)
        }
    }
    fn compile_array_index_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &ArrayIndexExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        compiler_bail!(source_context, "Unimplemented: Array support in the type system is not implemented yet");
    }
    fn compile_integer_constant_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &IntegerConstantExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};
        Self::attach_source_context(scope, &source_context, self.function_definition.add_int_constant_instruction(expression.constant_value).with_source_context(&source_context)?);
        Ok(ExpressionValueType::Int)
    }
    fn compile_block_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BlockExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Compile all statements in the block and then push the return value expression on the stack
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let block_scope = scope.declare_scope("block", CompilerLexicalScopeClass::Block(block_declaration.clone()), DeclarationVisibility::Private, &source_context.line_context)?;
        let block_start_instruction_index = self.function_definition.current_instruction_count();
        for statement in &expression.statements {
            self.compile_statement(&block_scope, statement)?;
        }
        let return_value_expression_type = self.compile_expression(&block_scope, &expression.return_value_expression)?;
        block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
            start_instruction_index: block_start_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };
        Ok(return_value_expression_type)
    }
    fn compile_conditional_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &ConditionalExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Evaluate the condition, and jump to the else block if it is zero
        let condition_expression_type = self.compile_expression(scope, &expression.condition_expression)?;
        Self::check_expression_type(&source_context, ExpressionValueType::Int, condition_expression_type)?;
        let (jump_to_else_instruction_index, jump_to_else_block_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, jump_to_else_instruction_index);

        // We did not jump to the else block, which means the condition was true. Evaluate the true branch and jump to the end
        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let then_branch_block = scope.declare_scope("then", CompilerLexicalScopeClass::Block(then_block_declaration.clone()), DeclarationVisibility::Private, &source_context.line_context)?;
        let then_instruction_index = self.function_definition.current_instruction_count();
        let then_expression_type = self.compile_expression(&then_branch_block, &expression.true_expression)?;

        let (jump_to_end_instruction_index, jump_to_end_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch).with_source_context(&source_context)?;
        Self::attach_source_context(&then_branch_block, &source_context, jump_to_end_instruction_index);
        then_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
            start_instruction_index: then_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };

        let else_block_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_else_block_fixup, else_block_instruction_index).with_source_context(&source_context)?;

        // We jumped to the else block, evaluate the false branch
        let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let else_branch_block = scope.declare_scope("else", CompilerLexicalScopeClass::Block(else_block_declaration.clone()), DeclarationVisibility::Private, &source_context.line_context)?;
        let else_expression_type = self.compile_expression(&else_branch_block, &expression.false_expression)?;
        else_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
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
    fn compile_binary_operator(&mut self, scope: &Rc<CompilerLexicalScope>, left_side_type: ExpressionValueType, right_side_type: ExpressionValueType, source_context: &CompilerSourceContext, operator: BinaryOperator) -> CompilerResult<ExpressionValueType> {
        if left_side_type != right_side_type {
            compiler_bail!(source_context, "Expression type mismatch: got expression of type {} on the left side of binary operator, and expression of type {} on the right side", left_side_type, right_side_type);
        }
        match operator {
            // Bitwise operators
            BinaryOperator::BitwiseOr => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Or).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::BitwiseXor => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Xor).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::BitwiseAnd => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::And).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::BitwiseShiftLeft => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Shl).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::BitwiseShiftRight => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Shr).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            // Arithmetic operators
            BinaryOperator::ArithmeticAdd => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Add).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::ArithmeticSubtract => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::ArithmeticMultiply => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Mul).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::ArithmeticDivide => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Div).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::ArithmeticRemainder => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Rem).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            // Logical operators
            BinaryOperator::LogicalLess => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                // left < right = (left - right) < 0
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Lz).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::LogicalMore => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                // left > right = (left - right) > 0 = (right - left) < 0
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Permute).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Lz).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::LogicalLessEquals => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                // left <= right = (left - right) <= 0
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Lez).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::LogicalMoreEquals => {
                Self::check_expression_type(source_context, ExpressionValueType::Int, left_side_type)?;
                // left >= right = (left - right) >= 0 = (right - left) <= 0
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Permute).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Lez).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::Equals => {
                // Use Ez for integer comparison, and generic Equals for everything else
                if left_side_type == ExpressionValueType::Int {
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Ez).with_source_context(source_context)?);
                } else {
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Equals).with_source_context(source_context)?);
                }
                Ok(ExpressionValueType::Int)
            }
            BinaryOperator::NotEquals => {
                // Use Ez for integer comparison, and generic Equals for everything else
                if left_side_type == ExpressionValueType::Int {
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Sub).with_source_context(source_context)?);
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Ez).with_source_context(source_context)?);
                } else {
                    Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Equals).with_source_context(source_context)?);
                }
                Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Ez).with_source_context(source_context)?);
                Ok(ExpressionValueType::Int)
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
        Self::check_expression_type(&source_context, ExpressionValueType::Int, left_expression_type)?;

        // Duplicate the left side value
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Dup).with_source_context(source_context)?);
        if operator == BinaryOperator::ShortCircuitOr {
            // If the left side value is not zero, jump to the end of the operator (and return that value, which is non-zero in this case)
            Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Ez).with_source_context(source_context)?);
        } else if operator == BinaryOperator::ShortCircuitAnd {
            // If the left side value is zero, jump to the end of the operator (and return that value, which is zero in this case)
        } else {
            compiler_bail!(source_context, "Only short circuited operators are supported by compile_short_circuit_binary_operator");
        }
        let (jump_to_end_instruction_index, jump_to_end_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(source_context)?;
        Self::attach_source_context(scope, source_context, jump_to_end_instruction_index);

        // We will end up here if the left side value is not zero. Now we can execute the right side and return its value
        // Make sure to drop the duplicated left side beforehand though. We duplicate the value to remove the need to generate the else branch (since Branchz consumes the value)
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::Pop).with_source_context(source_context)?);
        let right_expression_type = self.compile_expression(scope, &right_side)?;
        Self::check_expression_type(&source_context, ExpressionValueType::Int, right_expression_type)?;

        let end_instruction_index = self.function_definition.current_instruction_count();
        self.function_definition.fixup_control_flow_instruction(jump_to_end_fixup, end_instruction_index).with_source_context(&source_context)?;
        Ok(ExpressionValueType::Int)
    }
    fn compile_binary_expression(&mut self, scope: &Rc<CompilerLexicalScope>, expression: &BinaryExpression) -> CompilerResult<ExpressionValueType> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: expression.source_context.clone()};

        // Use shared routine for handling operators that do not short circuit and can have both expressions evaluated immediately
        if expression.operator != BinaryOperator::ShortCircuitAnd && expression.operator != BinaryOperator::ShortCircuitOr {
            let left_expression_type = self.compile_expression(scope, &expression.left_expression)?;
            let right_expression_type = self.compile_expression(scope, &expression.right_expression)?;

            self.compile_binary_operator(scope, left_expression_type, right_expression_type, &source_context, expression.operator)
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
                Self::check_expression_type(&source_context, ExpressionValueType::Typename, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutGetAlignment).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Int)
            }
            UnaryOperator::StructSizeOf => {
                Self::check_expression_type(&source_context, ExpressionValueType::Typename, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutGetSize).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Int)
            }
            UnaryOperator::StructMakePointer => {
                Self::check_expression_type(&source_context, ExpressionValueType::Typename, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutCreatePointer).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Typename)
            }
            UnaryOperator::BoolNegate => {
                Self::check_expression_type(&source_context, ExpressionValueType::Int, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::Ez).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Int)
            }
            UnaryOperator::BitwiseInverse => {
                Self::check_expression_type(&source_context, ExpressionValueType::Int, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::ReverseBits).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Int)
            }
            UnaryOperator::ArithmeticNegate => {
                Self::check_expression_type(&source_context, ExpressionValueType::Int, inner_expression_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::Neg).with_source_context(&source_context)?);
                Ok(ExpressionValueType::Int)
            }
        }
    }
    fn find_or_define_constant_slot(&mut self, slot_type: GospelValueType, binding: GospelSourceSlotBinding, source_context: &CompilerSourceContext) -> CompilerResult<u32> {
        if let Some(existing_slot_index) = self.constant_slot_lookup.get(&(slot_type, binding.clone())) {
            return Ok(*existing_slot_index);
        }
        let new_slot_index = self.function_definition.add_slot(slot_type, binding.clone()).with_source_context(source_context)?;
        self.constant_slot_lookup.insert((slot_type, binding.clone()), new_slot_index);
        Ok(new_slot_index)
    }
    fn compile_argument_value(&mut self, scope: &Rc<CompilerLexicalScope>, source_context: &CompilerSourceContext, argument_declaration: &Rc<CompilerLexicalDeclaration>, argument_type: ExpressionValueType) -> CompilerResult<ExpressionValueType> {
        let argument_index = self.argument_source_declarations.iter()
            .enumerate()
            .find(|(_, parameter_declaration)| Rc::ptr_eq(*parameter_declaration, &argument_declaration))
            .map(|(parameter_index, _)| parameter_index)
            .ok_or_else(|| compiler_error!(source_context, "Could not find function argument for parameter {}", argument_declaration.name))?;

        let slot_binding = GospelSourceSlotBinding::ArgumentValue(argument_index as u32);
        let slot_index = self.find_or_define_constant_slot(CompilerInstance::convert_value_type(argument_type), slot_binding, source_context)?;

        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, slot_index).with_source_context(source_context)?);
        Ok(argument_type)
    }
    fn compile_lexical_declaration_access(&mut self, scope: &Rc<CompilerLexicalScope>, source_context: &CompilerSourceContext, declaration: &Rc<CompilerLexicalDeclaration>) -> CompilerResult<ExpressionValueType> {
        match &declaration.class {
            CompilerLexicalDeclarationClass::LocalVariable(local_variable) => {
                // When compiling inline struct definitions, we can capture local variables from the current scope, which will be converted to implicit parameters
                // Such local variables do not belong to the current function, and should be looked up as parameters instead. So only treat local variable as actual local variable if it is declared within this functions scope
                if declaration.parent.upgrade().map(|x| x.is_child_of(&self.function_scope)).unwrap_or(false) {
                    Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, local_variable.value_slot).with_source_context(source_context)?);
                    Ok(local_variable.variable_type)
                } else {
                    self.compile_argument_value(scope, source_context, &declaration, local_variable.variable_type)
                }
            }
            CompilerLexicalDeclarationClass::Parameter(parameter_type) => {
                self.compile_argument_value(scope, source_context, &declaration, parameter_type.clone())
            }
            CompilerLexicalDeclarationClass::GlobalData((global_variable_expression_type, global_variable_name)) => {
                let slot_binding = GospelSourceSlotBinding::StaticValue(GospelSourceStaticValue::GlobalVariableValue(global_variable_name.clone()));
                let slot_index = self.find_or_define_constant_slot(CompilerInstance::convert_value_type(*global_variable_expression_type), slot_binding, source_context)?;

                Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, slot_index).with_source_context(source_context)?);
                Ok(*global_variable_expression_type)
            }
            _ => Err(compiler_error!(source_context, "Declaration {} does not name a local or global variable or template parameter", declaration.name))
        }
    }
    fn load_function_and_implicit_arguments(&mut self, scope: &Rc<CompilerLexicalScope>, function: &CompilerFunctionReference, source_context: &CompilerSourceContext) -> CompilerResult<usize> {
        // Load the function object from the constant slot
        let function_slot_binding = GospelSourceSlotBinding::StaticValue(GospelSourceStaticValue::FunctionId(function.function.clone()));
        let function_slot_index = self.find_or_define_constant_slot(GospelValueType::Closure, function_slot_binding, source_context)?;
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, function_slot_index).with_source_context(source_context)?);

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
            self.compile_lexical_declaration_access(scope, source_context, &implicit_parameter)?;
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
                    Self::check_expression_type(source_context, parameter_types[parameter_index].parameter_type, provided_parameter_type)?;
                    // Cache the parameter value expression in case we need it as an input for evaluation of the default argument value down the line
                    currently_provided_parameter_expressions.push(parameter_expressions[parameter_index].clone());
                } else if let Some(default_parameter_value_provider) = &parameter_types[parameter_index].default_value {
                    // This function has a default parameter value, so compile the call to the function producing it
                    // Such a function can receive implicit parameters from the parent scope, as well as the values of the parameters before this one
                    let default_value_type = self.compile_static_function_call(scope, default_parameter_value_provider, source_context, Some(&currently_provided_parameter_expressions), true)?;
                    Self::check_expression_type(source_context, parameter_types[parameter_index].parameter_type, default_value_type)?;
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
        Self::attach_source_context(scope, source_context, self.function_definition.add_variadic_instruction(GospelOpcode::Call, function_parameter_count as u32).with_source_context(source_context)?);
        Ok(function.signature.return_value_type)
    }
    fn compile_implicitly_bound_function_closure_or_call(&mut self, scope: &Rc<CompilerLexicalScope>, function: &CompilerFunctionReference, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        // Load the function and the implicit arguments on the stack
        let implicit_parameter_count = self.load_function_and_implicit_arguments(scope, function, source_context)?;

        // If this function has explicit parameters, we have to bind the closure with implicit values and return it directly
        if function.signature.explicit_parameters.is_some() {
            Self::attach_source_context(scope, source_context, self.function_definition.add_variadic_instruction(GospelOpcode::BindClosure, implicit_parameter_count as u32).with_source_context(source_context)?);
            Ok(ExpressionValueType::Closure)
        } else {
            // This function has no implicit parameters, so we can call it immediately to retrieve its value
            Self::attach_source_context(scope, source_context, self.function_definition.add_variadic_instruction(GospelOpcode::Call, implicit_parameter_count as u32).with_source_context(source_context)?);
            Ok(function.signature.return_value_type)
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
                self.compile_lexical_declaration_access(scope, &source_context, &declaration)
            }
            CompilerLexicalNode::Scope(scope_declaration) => {
                match &scope_declaration.class {
                    CompilerLexicalScopeClass::Function(data_closure) => {
                        self.compile_static_function_call(scope, &data_closure.borrow().function_reference, &source_context, expression.template_arguments.as_ref(), false)
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
        Self::check_expression_type(&scope.source_context, return_value_type, self.function_closure.signature.return_value_type)?;
        Self::attach_source_context(scope, &actual_source_context, self.function_definition.add_simple_instruction(GospelOpcode::ReturnValue).with_source_context(&actual_source_context)?);
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
                Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::LoadSlot, local_variable.value_slot).with_source_context(&source_context)?);
                let right_side_type = self.compile_expression(scope, &statement.assignment_expression)?;
                let operator_result_type = self.compile_binary_operator(scope, local_variable.variable_type, right_side_type, &source_context, assignment_operator)?;

                Self::check_expression_type(&source_context, local_variable.variable_type, operator_result_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, local_variable.value_slot).with_source_context(&source_context)?);
            } else {
                // This is a direct assignment
                let right_side_type = self.compile_expression(scope, &statement.assignment_expression)?;
                Self::check_expression_type(&source_context, local_variable.variable_type, right_side_type)?;
                Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, local_variable.value_slot).with_source_context(&source_context)?);
            }
            Ok({})
        } else {
            compiler_bail!(source_context, "Expected {} to refer to a local variable, but it refers to {} instead", assignment_identifier, resolved_node);
        }
    }
    fn compile_declaration_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &DeclarationStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};

        let slot_index = self.function_definition.add_slot(CompilerInstance::convert_value_type(statement.value_type), GospelSourceSlotBinding::Uninitialized).with_source_context(&source_context)?;
        let local_variable = CompilerLocalVariable{value_slot: slot_index, variable_type: statement.value_type};
        scope.declare(statement.name.as_str(), CompilerLexicalDeclarationClass::LocalVariable(local_variable), DeclarationVisibility::Private, &statement.source_context)?;

        if let Some(variable_initializer) = &statement.initializer {
            let initializer_type = self.compile_expression(scope, variable_initializer)?;
            Self::check_expression_type(&source_context, statement.value_type, initializer_type)?;
            Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index).with_source_context(&source_context)?);
        }
        Ok({})
    }
    fn compile_conditional_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &ConditionalStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let condition_value_type = self.compile_expression(scope, &statement.condition_expression)?;
        Self::check_expression_type(&scope.source_context, condition_value_type, ExpressionValueType::Int)?;

        let (condition_instruction_index, condition_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, condition_instruction_index);

        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let then_scope = scope.declare_scope_generated_name("then", CompilerLexicalScopeClass::Block(then_block_declaration.clone()), &source_context.line_context)?;
        let then_instruction_index=  self.function_definition.current_instruction_count();
        self.compile_statement(&then_scope, &statement.then_statement)?;

        if let Some(else_statement) = &statement.else_statement {
            // We have an else statement, so we need to jump to the end of the conditional statement after then branch is done
            let (then_instruction_index, then_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch).with_source_context(&then_scope.source_context)?;
            Self::attach_source_context(&then_scope, &source_context, then_instruction_index);
            let else_branch_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: then_instruction_index,
                end_instruction_index: else_branch_instruction_index,
            };

            let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
            let else_scope = scope.declare_scope_generated_name("else", CompilerLexicalScopeClass::Block(else_block_declaration.clone()), &statement.source_context)?;
            self.compile_statement(&else_scope, &else_statement)?;
            else_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: else_branch_instruction_index,
                end_instruction_index: self.function_definition.current_instruction_count(),
            };

            self.function_definition.fixup_control_flow_instruction(condition_fixup, else_branch_instruction_index).with_source_context(&then_scope.source_context)?;
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            self.function_definition.fixup_control_flow_instruction(then_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        } else {
            // No else statement, just fix up condition to jump to the end of then branch if it is zero
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: then_instruction_index,
                end_instruction_index: condition_end_instruction_index,
            };
            self.function_definition.fixup_control_flow_instruction(condition_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        }
        Ok({})
    }
    fn compile_block_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &BlockStatement) -> CompilerResult<()> {
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let block_scope = scope.declare_scope_generated_name("block", CompilerLexicalScopeClass::Block(block_declaration.clone()), &statement.source_context)?;
        let block_start_instruction_index = self.function_definition.current_instruction_count();
        for inner_statement in &statement.statements {
            self.compile_statement(&block_scope, inner_statement)?;
        }
        block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
            start_instruction_index: block_start_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };
        Ok({})
    }
    fn compile_while_loop_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &WhileLoopStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let loop_start_instruction_index = self.function_definition.current_instruction_count();

        let loop_condition_value_type = self.compile_expression(scope, &statement.condition_expression)?;
        Self::check_expression_type(&source_context, loop_condition_value_type, ExpressionValueType::Int)?;
        let (loop_condition_instruction_index, loop_condition_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, loop_condition_instruction_index);

        let loop_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: Some(CompilerLoopCodegenData::default())}));
        let loop_scope = scope.declare_scope_generated_name("loop", CompilerLexicalScopeClass::Block(loop_declaration.clone()), &source_context.line_context)?;
        self.compile_statement(&loop_scope, &statement.loop_body_statement)?;

        Self::attach_source_context(scope, &source_context, self.function_definition.add_control_flow_instruction_no_fixup(GospelOpcode::Branch, loop_start_instruction_index).with_source_context(&loop_scope.source_context)?);
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

        let (break_instruction_index, break_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, break_instruction_index);
        innermost_loop_statement.borrow_mut().loop_codegen_data.as_mut().unwrap().loop_finish_fixups.push(break_fixup);
        Ok({})
    }
    fn compile_continue_loop_statement(&mut self, scope: &Rc<CompilerLexicalScope>, statement: &SimpleStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let innermost_loop_statement = scope.iterate_scope_chain_inner_first()
            .filter_map(|x| if let CompilerLexicalScopeClass::Block(y) = &x.class { Some(y.clone()) } else { None })
            .find(|x| x.borrow().loop_codegen_data.is_some())
            .ok_or_else(|| compiler_error!(source_context, "continue; cannot be used outside the loop body"))?;

        let (continue_instruction_index, continue_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, continue_instruction_index);
        innermost_loop_statement.borrow_mut().loop_codegen_data.as_mut().unwrap().loop_start_fixups.push(continue_fixup);
        Ok({})
    }
    fn compile_type_layout_initialization(&mut self, scope: &Rc<CompilerLexicalScope>, type_name: &str) -> CompilerResult<u32> {
        let source_context = self.function_scope.source_context.clone();
        let slot_index = self.function_definition.add_slot(GospelValueType::TypeLayout, GospelSourceSlotBinding::Uninitialized).with_source_context(&source_context)?;
        let local_variable = CompilerLocalVariable{value_slot: slot_index, variable_type: ExpressionValueType::Typename};
        scope.declare("@struct", CompilerLexicalDeclarationClass::LocalVariable(local_variable), DeclarationVisibility::Private, &source_context.line_context)?;

        Self::attach_source_context(scope, &source_context, self.function_definition.add_string_instruction(GospelOpcode::TypeLayoutAllocate, type_name).with_source_context(&source_context)?);
        Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index).with_source_context(&source_context)?);
        Ok(slot_index)
    }
    fn compile_type_layout_metadata_struct_initialization(&mut self, scope: &Rc<CompilerLexicalScope>, struct_meta_layout: &CompilerStructMetaLayoutReference) -> CompilerResult<u32> {
        let source_context = self.function_scope.source_context.clone();
        let slot_index = self.function_definition.add_slot(GospelValueType::Struct, GospelSourceSlotBinding::Uninitialized).with_source_context(&source_context)?;
        let local_variable = CompilerLocalVariable{value_slot: slot_index, variable_type: ExpressionValueType::MetaStruct };
        scope.declare("@metastruct", CompilerLexicalDeclarationClass::LocalVariable(local_variable), DeclarationVisibility::Private, &source_context.line_context)?;

        Self::attach_source_context(scope, &source_context, self.function_definition.add_struct_instruction(GospelOpcode::StructAllocate, struct_meta_layout.reference.clone()).with_source_context(&source_context)?);
        Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, slot_index).with_source_context(&source_context)?);
        Ok(slot_index)
    }
    fn compile_coerce_alignment_expression(&mut self, scope: &Rc<CompilerLexicalScope>, alignment_expression: &Expression, source_context: &CompilerSourceContext) -> CompilerResult<ExpressionValueType> {
        let source_alignment_expression_type = self.compile_expression(scope, alignment_expression)?;

        // Typename is a valid parameter to alignas(T) operator, and should be automatically coerced to the integral alignment
        if source_alignment_expression_type == ExpressionValueType::Typename {
            Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutGetAlignment).with_source_context(source_context)?);
            Ok(ExpressionValueType::Int)
        } else {
            // Should be an integer alignment otherwise
            Self::check_expression_type(source_context, ExpressionValueType::Int, source_alignment_expression_type)?;
            Ok(ExpressionValueType::Int)
        }
    }
    fn compile_type_layout_alignment_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, alignment_expression: &Expression, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_slot_index).with_source_context(&source_context)?);

        let alignment_expression_type = self.compile_coerce_alignment_expression(scope, alignment_expression, source_context)?;
        Self::check_expression_type(source_context, ExpressionValueType::Int, alignment_expression_type)?;
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutAlign).with_source_context(&source_context)?);

        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, type_layout_slot_index).with_source_context(&source_context)?);
        Ok({})
    }
    fn compile_type_layout_base_class_expression(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, base_class_expression: &Expression, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_slot_index).with_source_context(&source_context)?);

        let base_class_expression_type = self.compile_expression(scope, base_class_expression)?;
        Self::check_expression_type(source_context, ExpressionValueType::Typename, base_class_expression_type)?;
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutDefineBaseClass).with_source_context(&source_context)?);

        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, type_layout_slot_index).with_source_context(&source_context)?);
        Ok({})
    }
    fn compile_type_layout_block_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, declaration: &BlockDeclaration) -> CompilerResult<()> {
        let block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let block_scope = scope.declare_scope_generated_name("block", CompilerLexicalScopeClass::Block(block_declaration.clone()), &declaration.source_context)?;
        let block_instruction_index = self.function_definition.current_instruction_count();
        for inner_declaration in &declaration.declarations {
            self.compile_type_layout_inner_declaration(&block_scope, type_layout_slot_index, type_layout_metadata_slot_index, type_layout_metadata_struct, inner_declaration)?;
        }
        block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
            start_instruction_index: block_instruction_index,
            end_instruction_index: self.function_definition.current_instruction_count(),
        };
        Ok({})
    }
    fn compile_type_layout_conditional_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, declaration: &ConditionalDeclaration) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};

        let condition_value_type = self.compile_expression(scope, &declaration.condition_expression)?;
        Self::check_expression_type(&source_context, condition_value_type, ExpressionValueType::Int)?;
        let (condition_instruction_index, condition_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branchz).with_source_context(&source_context)?;
        Self::attach_source_context(scope, &source_context, condition_instruction_index);

        let then_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
        let then_scope = scope.declare_scope_generated_name("then", CompilerLexicalScopeClass::Block(then_block_declaration.clone()), &declaration.source_context)?;
        let then_branch_instruction_index = self.function_definition.current_instruction_count();
        self.compile_type_layout_inner_declaration(&then_scope, type_layout_slot_index, type_layout_metadata_slot_index, type_layout_metadata_struct, &declaration.then_branch)?;

        if let Some(else_statement) = &declaration.else_branch {
            // We have an else statement, so we need to jump to the end of the conditional statement after then branch is done
            let (then_instruction_index, then_fixup) = self.function_definition.add_control_flow_instruction(GospelOpcode::Branch).with_source_context(&then_scope.source_context)?;
            Self::attach_source_context(scope, &source_context, then_instruction_index);
            let else_branch_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: then_branch_instruction_index,
                end_instruction_index: else_branch_instruction_index,
            };

            let else_block_declaration = Rc::new(RefCell::new(CompilerBlockDeclaration{debug_data: Some(CompilerDebugData::default()), loop_codegen_data: None}));
            let else_scope = scope.declare_scope_generated_name("else", CompilerLexicalScopeClass::Block(else_block_declaration.clone()), &declaration.source_context)?;
            self.compile_type_layout_inner_declaration(&else_scope, type_layout_slot_index, type_layout_metadata_slot_index, type_layout_metadata_struct, &else_statement)?;
            else_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: else_branch_instruction_index,
                end_instruction_index: self.function_definition.current_instruction_count(),
            };

            self.function_definition.fixup_control_flow_instruction(condition_fixup, else_branch_instruction_index).with_source_context(&then_scope.source_context)?;
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            self.function_definition.fixup_control_flow_instruction(then_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        } else {
            // No else statement, just fix up condition to jump to the end of then branch if it is zero
            let condition_end_instruction_index = self.function_definition.current_instruction_count();
            then_block_declaration.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: then_branch_instruction_index,
                end_instruction_index: condition_end_instruction_index,
            };
            self.function_definition.fixup_control_flow_instruction(condition_fixup, condition_end_instruction_index).with_source_context(&then_scope.source_context)?;
        }
        Ok({})
    }
    fn compile_type_layout_metadata_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, field_name: &str, function_reference: &CompilerFunctionReference, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        // Take metadata struct from the slot
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_metadata_slot_index).with_source_context(source_context)?);

        // Push the struct closure or resolved type layout on the stack
        let metadata_field_value_type = self.compile_implicitly_bound_function_closure_or_call(scope, &function_reference, source_context)?;
        let metadata_field_index = type_layout_metadata_struct.signature.find_member_index_checked(field_name, metadata_field_value_type, source_context)?;

        // Set the meta struct field value and store the struct back to the slot
        Self::attach_source_context(scope, source_context, self.function_definition.add_struct_local_member_access_instruction(GospelOpcode::StructSetLocalField, type_layout_metadata_struct.reference.clone(), metadata_field_index as u32).with_source_context(source_context)?);
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, type_layout_metadata_slot_index).with_source_context(source_context)?);
        Ok({})
    }
    fn compile_type_layout_struct_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, declaration: &StructStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        let struct_reference = CompilerInstance::compile_struct_statement(scope, &declaration, None, self.nested_declaration_visibility())?;

        let metadata_field_name = declaration.name.as_ref().ok_or_else(|| compiler_error!(&source_context, "Unnamed struct declaration in top level scope. All top level structs must have a name"))?;
        self.compile_type_layout_metadata_declaration(scope, type_layout_metadata_slot_index, type_layout_metadata_struct, metadata_field_name.as_str(), &struct_reference, &source_context)
    }
    fn compile_type_layout_data_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, declaration: &DataStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        let data_reference = CompilerInstance::compile_data_statement(scope, &declaration, self.nested_declaration_visibility())?;

        self.compile_type_layout_metadata_declaration(scope, type_layout_metadata_slot_index, type_layout_metadata_struct, declaration.name.as_str(), &data_reference, &source_context)
    }
    fn compile_type_layout_member_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, declaration: &MemberDeclaration) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: declaration.source_context.clone()};
        Self::attach_source_context(&scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_slot_index).with_source_context(&source_context)?);

        // Align the current offset to the required alignment first if one is present
        if let Some(alignment_expression) = &declaration.alignment_expression {
            let alignment_expression_type = self.compile_coerce_alignment_expression(scope, alignment_expression, &source_context)?;
            Self::check_expression_type(&source_context, ExpressionValueType::Int, alignment_expression_type)?;
            Self::attach_source_context(scope, &source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutAlign).with_source_context(&source_context)?);
        }

        // Compile member type expression
        let member_type_expression_type = self.compile_expression(scope, &declaration.member_type_expression)?;
        Self::check_expression_type(&source_context, ExpressionValueType::Typename, member_type_expression_type)?;

        if let Some(array_size_expression) = &declaration.array_size_expression {
            // If there is array size expression, this is an array member
            let array_size_expression_type = self.compile_expression(scope, array_size_expression)?;
            Self::check_expression_type(&source_context, ExpressionValueType::Int, array_size_expression_type)?;
            Self::attach_source_context(scope, &source_context, self.function_definition.add_string_instruction(GospelOpcode::TypeLayoutDefineArrayMember, declaration.name.as_str()).with_source_context(&source_context)?);

        } else if let Some(bitfield_width_expression) = &declaration.bitfield_width_expression {
            // If there is a bitfield width expression, this is a bitfield member
            let bitfield_width_expression_type = self.compile_expression(scope, bitfield_width_expression)?;
            Self::check_expression_type(&source_context, ExpressionValueType::Int, bitfield_width_expression_type)?;
            Self::attach_source_context(scope, &source_context, self.function_definition.add_string_instruction(GospelOpcode::TypeLayoutDefineBitfieldMember, declaration.name.as_str()).with_source_context(&source_context)?);

        } else {
            // Otherwise, this is a normal member
            Self::attach_source_context(scope, &source_context, self.function_definition.add_string_instruction(GospelOpcode::TypeLayoutDefineMember, declaration.name.as_str()).with_source_context(&source_context)?);
        }

        Self::attach_source_context(scope, &source_context, self.function_definition.add_slot_instruction(GospelOpcode::StoreSlot, type_layout_slot_index).with_source_context(&source_context)?);
        Ok({})
    }
    fn compile_type_layout_inner_declaration(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, type_layout_metadata_slot_index: u32, type_layout_metadata_struct: &CompilerStructMetaLayoutReference, inner_declaration: &StructInnerDeclaration) -> CompilerResult<()> {
        match inner_declaration {
            StructInnerDeclaration::BlockDeclaration(block_declaration) => {
                self.compile_type_layout_block_declaration(scope, type_layout_slot_index, type_layout_metadata_slot_index, type_layout_metadata_struct, &*block_declaration)
            }
            StructInnerDeclaration::ConditionalDeclaration(conditional_declaration) => {
                self.compile_type_layout_conditional_declaration(scope, type_layout_slot_index, type_layout_metadata_slot_index, type_layout_metadata_struct, &*conditional_declaration)
            }
            StructInnerDeclaration::NestedStructDeclaration(struct_declaration) => {
                self.compile_type_layout_struct_declaration(scope, type_layout_metadata_slot_index, type_layout_metadata_struct, &*struct_declaration)
            }
            StructInnerDeclaration::DataDeclaration(data_declaration) => {
                self.compile_type_layout_data_declaration(scope, type_layout_metadata_slot_index, type_layout_metadata_struct, &*data_declaration)
            }
            StructInnerDeclaration::MemberDeclaration(member_declaration) => {
                self.compile_type_layout_member_declaration(scope, type_layout_slot_index, &*member_declaration)
            }
            StructInnerDeclaration::EmptyDeclaration => { Ok({}) }
        }
    }
    fn compile_type_layout_finalization(&mut self, scope: &Rc<CompilerLexicalScope>, type_layout_slot_index: u32, type_layout_metadata_slot_index: u32, source_context: &CompilerSourceContext) -> CompilerResult<()> {
        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_slot_index).with_source_context(&source_context)?);

        Self::attach_source_context(scope, source_context, self.function_definition.add_slot_instruction(GospelOpcode::TakeSlot, type_layout_metadata_slot_index).with_source_context(&source_context)?);
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutSetMetadata).with_source_context(&source_context)?);

        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::TypeLayoutFinalize).with_source_context(&source_context)?);
        Self::attach_source_context(scope, source_context, self.function_definition.add_simple_instruction(GospelOpcode::ReturnValue).with_source_context(&source_context)?);
        Ok({})
    }
    fn check_expression_type(context: &CompilerSourceContext, expected_type: ExpressionValueType, actual_type: ExpressionValueType) -> CompilerResult<()> {
        if expected_type != actual_type {
            compiler_bail!(context, "Expression type mismatch: expected {}, got {}", expected_type, actual_type);
        }
        Ok({})
    }
    fn attach_source_context(scope: &Rc<CompilerLexicalScope>, source_context: &CompilerSourceContext, instruction_index: u32) {
        if let CompilerLexicalScopeClass::Function(function_declaration) = &scope.class {
            if let Some(debug_data) = &mut function_declaration.borrow_mut().debug_data {
                debug_data.instruction_line_mappings.insert(instruction_index, source_context.line_context.line_number as u32);
            }
        } else if let CompilerLexicalScopeClass::Block(block_declaration) = &scope.class {
            if let Some(debug_data) = &mut block_declaration.borrow_mut().debug_data {
                debug_data.instruction_line_mappings.insert(instruction_index, source_context.line_context.line_number as u32);
            }
        }
    }
    fn commit(self) -> CompilerResult<CompilerFunctionReference> {
        if let Some(module_visitor) = self.function_scope.module_visitor() {
            if let Err(error) = module_visitor.borrow_mut().define_function(self.function_definition) {
                compiler_bail!(&self.function_scope.source_context, "Failed to define function {}: {}", self.function_scope.full_scope_name(), error.to_string());
            }
        }
        Ok(self.function_closure)
    }
}

#[derive(Debug)]
pub struct CompilerModuleBuilder {
    module_scope: Rc<CompilerLexicalScope>,
    /// This is not actually "dead code", this ensures that the compile instances lives as long as the reference to the module scope, which itself does not keep a hard reference to the compiler
    #[allow(dead_code)]
    compiler: Rc<CompilerInstance>,
}
impl CompilerModuleBuilder {
    pub fn compile_source_file(&self, source_file: ModuleSourceFile) -> CompilerResult<()> {
        let file_name_without_extension = PathBuf::from(source_file.file_name.as_str()).file_stem().map(|x| x.to_string_lossy().to_string()).unwrap();
        let file_scope = self.module_scope.declare_scope(&file_name_without_extension, CompilerLexicalScopeClass::SourceFile(source_file.file_name.clone()), DeclarationVisibility::Public, &ASTSourceContext::default())?;

        source_file.declarations.iter().map(|top_level_declaration| match top_level_declaration {
            ModuleTopLevelDeclaration::EmptyStatement => { Ok({}) }
            ModuleTopLevelDeclaration::ImportStatement(import_statement) => { CompilerInstance::compile_import_statement(&file_scope, import_statement) }
            ModuleTopLevelDeclaration::ExternStatement(extern_statement) => { CompilerInstance::compile_extern_statement(&file_scope, extern_statement) }
            ModuleTopLevelDeclaration::NamespaceStatement(namespace_statement) => { CompilerInstance::compile_namespace_statement(&file_scope, namespace_statement, DeclarationVisibility::Public) }
            ModuleTopLevelDeclaration::DataStatement(data_statement) => { CompilerInstance::compile_data_statement(&file_scope, data_statement, DeclarationVisibility::Public)?; Ok({}) }
            ModuleTopLevelDeclaration::StructStatement(struct_statement) => { CompilerInstance::compile_struct_statement(&file_scope, struct_statement, None, DeclarationVisibility::Public)?; Ok({}) }
        }).chain_compiler_result(|| compiler_error!(&file_scope.source_context, "Failed to compile source file"))
    }
}

#[derive(Debug, Clone)]
struct CompilerStructMetaMember {
    name: String,
    value_type: ExpressionValueType,
    declaration_source_contexts: Vec<CompilerSourceContext>,
}
#[derive(Debug, Clone, Default)]
struct CompilerStructMetaLayout {
    members: Vec<CompilerStructMetaMember>,
    member_lookup: HashMap<String, usize>,
}
impl CompilerStructMetaLayout {
    fn find_member_index_checked(&self, name: &str, value_type: ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<usize> {
        if let Some(member_index) = self.member_lookup.get(name).cloned() {
            if self.members[member_index].value_type != value_type {
                compiler_bail!(source_context, "Access to meta member {} with incompatible value type {} (member value type: {})", name, value_type, self.members[member_index].value_type);
            }
            Ok(member_index)
        } else {
            compiler_bail!(source_context, "Meta member with name {} not found in metadata struct", name);
        }
    }
    fn define_member_checked(&mut self, name: &str, value_type: ExpressionValueType, source_context: &CompilerSourceContext) -> CompilerResult<usize> {
        if let Some(existing_member_index) = self.member_lookup.get(name).cloned() {
            if self.members[existing_member_index].value_type != value_type {
               compiler_bail!(source_context, "Conflicting definition of meta member: Previous declaration of {} at {} was of type {}, attempting to redeclare as type {}",
                name, self.members[existing_member_index].declaration_source_contexts.first().as_ref().unwrap(), self.members[existing_member_index].value_type, value_type);
            }
            self.members[existing_member_index].declaration_source_contexts.push(source_context.clone());
            Ok(existing_member_index)
        } else {
            let new_struct_member = CompilerStructMetaMember{name: name.to_string(), value_type, declaration_source_contexts: vec![source_context.clone()]};
            let new_member_index = self.members.len();
            self.members.push(new_struct_member);
            self.member_lookup.insert(name.to_string(), new_member_index);
            Ok(new_member_index)
        }
    }
}

#[derive(Debug, Clone, Default)]
struct CompilerStructMetaLayoutReference {
    reference: GospelSourceObjectReference,
    signature: CompilerStructMetaLayout,
}

impl CompilerInstance {
    pub fn create() -> Rc<CompilerInstance> {
        Rc::new(CompilerInstance{module_scopes: RefCell::new(HashMap::new())})
    }
    pub fn define_module(self: &Rc<Self>, module_name: &str, module_visitor: Option<Rc<RefCell<dyn GospelModuleVisitor>>>) -> CompilerResult<CompilerModuleBuilder> {
        let source_context = CompilerSourceContext::default();
        if self.module_scopes.borrow().contains_key(module_name) {
            compiler_bail!(source_context, "Module {} is already defined", module_name);
        }
        if let Some(module_visitor_ref) = &module_visitor && module_visitor_ref.borrow().module_name() != Some(module_name.to_string()) {
            compiler_bail!(source_context, "Module {} visitor points to another module {}", module_name, module_visitor_ref.borrow().module_name().unwrap());
        }
        let new_module_scope = CompilerLexicalScope::create_root_scope(self, module_name.to_string(), module_visitor, &source_context);
        self.module_scopes.borrow_mut().insert(module_name.to_string(), new_module_scope.clone());
        Ok(CompilerModuleBuilder{module_scope: new_module_scope, compiler: self.clone()})
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
    fn convert_value_type(value_type: ExpressionValueType) -> GospelValueType {
        match value_type {
            ExpressionValueType::Int => GospelValueType::Integer,
            ExpressionValueType::Typename => GospelValueType::TypeLayout,
            ExpressionValueType::Closure => GospelValueType::Closure,
            ExpressionValueType::MetaStruct => GospelValueType::Struct,
        }
    }
    fn convert_access_specifier(value_type: DeclarationAccessSpecifier) -> DeclarationVisibility {
        match value_type {
            DeclarationAccessSpecifier::Public => DeclarationVisibility::Public,
            DeclarationAccessSpecifier::Internal => DeclarationVisibility::ModuleInternal,
            DeclarationAccessSpecifier::Local => DeclarationVisibility::FileLocal,
        }
    }
    fn compile_import_statement(scope: &Rc<CompilerLexicalScope>, statement: &ModuleImportStatement) -> CompilerResult<()> {
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
                NamespaceLevelDeclaration::EmptyStatement => { Ok({}) }
                NamespaceLevelDeclaration::NamespaceStatement(nested_namespace) => { Self::compile_namespace_statement(&current_scope, nested_namespace, DeclarationVisibility::Public) }
                NamespaceLevelDeclaration::DataStatement(data_statement) => { Self::compile_data_statement(&current_scope, data_statement, DeclarationVisibility::Public)?; Ok({}) }
                NamespaceLevelDeclaration::StructStatement(struct_statement) => { Self::compile_struct_statement(&current_scope, struct_statement, None, DeclarationVisibility::Public)?; Ok({}) }
            }
        }).chain_compiler_result(|| compiler_error!(source_context, "Failed to compile namespace declaration"))
    }
    fn compile_extern_statement(scope: &Rc<CompilerLexicalScope>, statement: &ExternStatement) -> CompilerResult<()> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let name = statement.global_name.clone();
        if statement.value_type != ExpressionValueType::Int {
            compiler_bail!(&source_context, "Global data can only be of Int type, attempting to declare global data {} as {}", name.as_str(), statement.value_type);
        }
        scope.declare(&name, CompilerLexicalDeclarationClass::GlobalData((statement.value_type, name.clone())), DeclarationVisibility::Public, &source_context.line_context)?;
        if let Some(visitor) = scope.module_visitor() {
            visitor.borrow_mut().declare_global(name.as_str()).with_source_context(&source_context)?;
        }
        Ok({})
    }
    fn compile_function_argument(source_function_scope: &Rc<CompilerLexicalScope>, source_function_closure: &RefCell<CompilerFunctionDeclaration>, template_argument: &TemplateArgument) -> CompilerResult<Rc<CompilerLexicalDeclaration>> {
        let source_context = CompilerSourceContext{file_name: source_function_scope.file_name(), line_context: template_argument.source_context.clone()};

        let default_value_closure = if let Some(argument_default_value_expression) = &template_argument.default_value {
            let argument_index = source_function_closure.borrow().function_reference.signature.explicit_parameters.as_ref().unwrap().len();
            let function_name = format!("{}@default_value@{}", source_function_scope.name.as_str(), argument_index);

            let function_closure = Rc::new(RefCell::new(CompilerFunctionDeclaration {
                debug_data: Some(CompilerDebugData::default()),
                function_reference: CompilerFunctionReference{
                    function: GospelSourceObjectReference::default(),
                    signature: CompilerFunctionSignature{ implicit_parameters: source_function_closure.borrow().function_reference.signature.implicit_parameters.clone(), ..CompilerFunctionSignature::default() }
                }
            }));
            let function_parent_scope = source_function_scope.parent_scope().unwrap();
            let function_scope = function_parent_scope.declare_scope(function_name.as_str(), CompilerLexicalScopeClass::Function(function_closure.clone()), source_function_scope.visibility, &source_context.line_context)?;

            function_closure.borrow_mut().function_reference.function = GospelSourceObjectReference{module_name: function_scope.module_name(), local_name: function_scope.full_scope_name()};
            function_closure.borrow_mut().function_reference.signature.return_value_type = template_argument.value_type;
            function_closure.borrow_mut().function_reference.signature.implicit_parameters = source_function_closure.borrow().function_reference.signature.implicit_parameters.clone();
            function_closure.borrow_mut().function_reference.signature.explicit_parameters = source_function_closure.borrow().function_reference.signature.explicit_parameters.clone();

            let mut function_builder = CompilerFunctionBuilder::create(&function_scope)?;
            function_builder.compile_return_value_expression(&function_builder.function_scope.clone(), &function_scope.source_context.line_context, argument_default_value_expression)?;
            function_closure.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: 0,
                end_instruction_index: function_builder.function_definition.current_instruction_count(),
            };
            Some(function_builder.commit()?)
        } else { None };

        let new_parameter_declaration = source_function_scope.declare(template_argument.name.as_str(),
          CompilerLexicalDeclarationClass::Parameter(template_argument.value_type), DeclarationVisibility::Private, &source_context.line_context)?;

        source_function_closure.borrow_mut().function_reference.signature.explicit_parameters.as_mut().unwrap().push(CompilerFunctionParameter{
            parameter_type: template_argument.value_type,
            default_value: default_value_closure,
            parameter_declaration: Rc::downgrade(&new_parameter_declaration),
        });
        Ok(new_parameter_declaration)
    }
    fn compile_function_declaration(scope: &Rc<CompilerLexicalScope>, function_name: &str, visibility: DeclarationVisibility, return_value_type: ExpressionValueType, template_declaration: Option<&TemplateDeclaration>, source_context: &ASTSourceContext) -> CompilerResult<CompilerFunctionBuilder> {
        let actual_source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: source_context.clone()};

        let implicit_parameters = scope.collect_implicit_scope_parameters();
        let function_closure = Rc::new(RefCell::new(CompilerFunctionDeclaration {
            debug_data: Some(CompilerDebugData::default()),
            function_reference: CompilerFunctionReference{
                function: GospelSourceObjectReference::default(),
                signature: CompilerFunctionSignature{ return_value_type, implicit_parameters, explicit_parameters: None }
            }
        }));
        let function_scope = scope.declare_scope(function_name, CompilerLexicalScopeClass::Function(function_closure.clone()), visibility, &actual_source_context.line_context)?;
        function_closure.borrow_mut().function_reference.function = GospelSourceObjectReference{module_name: scope.module_name(), local_name: function_scope.full_scope_name()};

        if let Some(template_arguments) = template_declaration {
            function_closure.borrow_mut().function_reference.signature.explicit_parameters = Some(Vec::new());
            for function_argument in &template_arguments.arguments {
                Self::compile_function_argument(&function_scope, &function_closure, function_argument)?;
            }
        }
        let function_builder = CompilerFunctionBuilder::create(&function_scope)?;
        Ok(function_builder)
    }
    fn compile_data_statement(scope: &Rc<CompilerLexicalScope>, statement: &DataStatement, default_visibility: DeclarationVisibility) -> CompilerResult<CompilerFunctionReference> {
        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        let mut function_builder = Self::compile_function_declaration(scope, statement.name.as_str(), visibility, statement.value_type, statement.template_declaration.as_ref(), &statement.source_context)?;
        function_builder.compile_return_value_expression(&function_builder.function_scope.clone(), &statement.source_context, &statement.initializer)?;
        if let CompilerLexicalScopeClass::Function(function_closure) = &function_builder.function_scope.class {
            function_closure.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: 0,
                end_instruction_index: function_builder.function_definition.current_instruction_count(),
            };
        }
        function_builder.commit()
    }
    fn populate_struct_meta_layout_from_declaration_recursive(scope: &Rc<CompilerLexicalScope>, declaration: &StructInnerDeclaration, meta_layout: &mut CompilerStructMetaLayout) -> CompilerResult<()> {
        match declaration {
            StructInnerDeclaration::DataDeclaration(data_statement) => {
                let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: data_statement.source_context.clone()};
                if data_statement.template_declaration.is_some() {
                    meta_layout.define_member_checked(data_statement.name.as_str(), ExpressionValueType::Closure, &source_context)?;
                } else {
                    meta_layout.define_member_checked(data_statement.name.as_str(), data_statement.value_type, &source_context)?;
                }
                Ok({})
            }
            StructInnerDeclaration::NestedStructDeclaration(struct_statement) => {
                let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: struct_statement.source_context.clone()};
                let name = struct_statement.name.as_ref().ok_or_else(|| compiler_error!(&source_context, "Unnamed struct declaration in top level scope. All top level structs must have a name"))?;
                if struct_statement.template_declaration.is_some() {
                    meta_layout.define_member_checked(name.as_str(), ExpressionValueType::Closure, &source_context)?;
                } else {
                    meta_layout.define_member_checked(name.as_str(), ExpressionValueType::Typename, &source_context)?;
                }
                Ok({})
            }
            StructInnerDeclaration::ConditionalDeclaration(conditional_statement) => {
                Self::populate_struct_meta_layout_from_declaration_recursive(scope, &conditional_statement.then_branch, meta_layout)?;
                if let Some(else_branch) = &conditional_statement.else_branch {
                    Self::populate_struct_meta_layout_from_declaration_recursive(scope, &else_branch, meta_layout)?;
                }
                Ok({})
            }
            StructInnerDeclaration::BlockDeclaration(block_statement) => {
                for inner_declaration in &block_statement.declarations {
                    Self::populate_struct_meta_layout_from_declaration_recursive(scope, inner_declaration, meta_layout)?;
                }
                Ok({})
            }
            StructInnerDeclaration::MemberDeclaration(_) => { Ok({}) }
            StructInnerDeclaration::EmptyDeclaration => { Ok({}) }
        }
    }
    fn compile_struct_meta_layout(struct_scope: &Rc<CompilerLexicalScope>, statement: &StructStatement) -> CompilerResult<CompilerStructMetaLayoutReference> {
        let source_context = CompilerSourceContext{file_name: struct_scope.file_name(), line_context: statement.source_context.clone()};
        let mut meta_layout = CompilerStructMetaLayout::default();
        for inner_declaration in &statement.declarations {
            Self::populate_struct_meta_layout_from_declaration_recursive(struct_scope, inner_declaration, &mut meta_layout)?;
        }

        let meta_layout_reference = Rc::new(RefCell::new(CompilerStructMetaLayoutReference{
            reference: GospelSourceObjectReference::default(),
            signature: meta_layout,
        }));
        let declaration_class = CompilerLexicalDeclarationClass::StructMetaLayout(meta_layout_reference.clone());
        let meta_layout_declaration = struct_scope.declare("@meta_layout", declaration_class, DeclarationVisibility::Public, &source_context.line_context)?;
        meta_layout_reference.borrow_mut().reference = GospelSourceObjectReference{module_name: struct_scope.module_name(), local_name: meta_layout_declaration.full_declaration_name()};

        if let Some(visitor) = struct_scope.module_visitor() {
            let compiled_struct_definition = GospelSourceStructDefinition{
                name: meta_layout_reference.borrow().reference.clone(),
                hidden: meta_layout_declaration.visibility != DeclarationVisibility::Public,
                fields: meta_layout_reference.borrow().signature.members.iter().map(|x| GospelSourceStructField{
                    field_name: Some(x.name.clone()), field_type: Self::convert_value_type(x.value_type)
                }).collect()
            };
            visitor.borrow_mut().define_struct(compiled_struct_definition).with_source_context(&source_context)?;
        }
        Ok(meta_layout_reference.borrow().clone())
    }
    fn compile_struct_statement(scope: &Rc<CompilerLexicalScope>, statement: &StructStatement, fallback_name: Option<&str>, default_visibility: DeclarationVisibility) -> CompilerResult<CompilerFunctionReference> {
        let source_context = CompilerSourceContext{file_name: scope.file_name(), line_context: statement.source_context.clone()};
        let function_name = statement.name.as_ref().map(|x| x.as_str()).or(fallback_name)
            .ok_or_else(|| compiler_error!(&source_context, "Unnamed struct declaration in top level scope. All top level structs must have a name"))?;

        let visibility = statement.access_specifier.map(|x| Self::convert_access_specifier(x)).unwrap_or(default_visibility);
        let mut function_builder = Self::compile_function_declaration(scope, function_name, visibility, ExpressionValueType::Typename, statement.template_declaration.as_ref(), &source_context.line_context)?;
        let struct_meta_layout = Self::compile_struct_meta_layout(&function_builder.function_scope, statement)?;

        let type_name = statement.name.clone().unwrap_or(String::from("<unnamed struct>"));
        let type_layout_slot_index = function_builder.compile_type_layout_initialization(&function_builder.function_scope.clone(), type_name.as_str())?;
        let type_layout_metadata_slot_index = function_builder.compile_type_layout_metadata_struct_initialization(&function_builder.function_scope.clone(), &struct_meta_layout)?;

        if let Some(alignment_expression) = &statement.alignment_expression {
            function_builder.compile_type_layout_alignment_expression(&function_builder.function_scope.clone(), type_layout_slot_index, alignment_expression, &source_context)?;
        }
        for base_class_expression in &statement.base_class_expressions {
            function_builder.compile_type_layout_base_class_expression(&function_builder.function_scope.clone(), type_layout_slot_index, base_class_expression, &source_context)?;
        }
        statement.declarations.iter().map(|struct_inner_declaration| {
            function_builder.compile_type_layout_inner_declaration(&function_builder.function_scope.clone(), type_layout_slot_index, type_layout_metadata_slot_index, &struct_meta_layout, struct_inner_declaration)
        }).chain_compiler_result(|| compiler_error!(&source_context, "Failed to compile struct definition"))?;

        function_builder.compile_type_layout_finalization(&function_builder.function_scope.clone(), type_layout_slot_index, type_layout_metadata_slot_index, &source_context)?;
        if let CompilerLexicalScopeClass::Function(function_closure) = &function_builder.function_scope.class {
            function_closure.borrow_mut().debug_data.as_mut().unwrap().block_range = CompilerInstructionRange{
                start_instruction_index: 0,
                end_instruction_index: function_builder.function_definition.current_instruction_count(),
            };
        }
        function_builder.commit()
    }
}

#[derive(Debug, Clone)]
struct CompilerLocalVariable {
    value_slot: u32,
    variable_type: ExpressionValueType,
}

#[derive(Debug, Clone, Display)]
enum CompilerLexicalDeclarationClass {
    #[strum(to_string = "global data")]
    GlobalData((ExpressionValueType, String)),
    #[strum(to_string = "parameter")]
    Parameter(ExpressionValueType),
    #[strum(to_string = "import")]
    Import(Weak<CompilerLexicalDeclaration>),
    #[strum(to_string = "namespace import")]
    NamespaceImport(Weak<CompilerLexicalScope>),
    #[strum(to_string = "local variable")]
    LocalVariable(CompilerLocalVariable),
    #[strum(to_string = "struct meta layout")]
    StructMetaLayout(Rc<RefCell<CompilerStructMetaLayoutReference>>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum DeclarationVisibility {
    Public,
    ModuleInternal,
    FileLocal,
    Private,
}
impl DeclarationVisibility {
    fn intersect(self, other: Self) -> Self {
        if self > other { self } else { other }
    }
}
#[derive(Debug, Clone)]
struct DeclarationVisibilityContext {
    module_name: Option<String>,
    file_name: Option<String>,
    source_scope: Option<Rc<CompilerLexicalScope>>,
}

#[derive(Debug, Clone)]
struct CompilerLexicalDeclaration {
    parent: Weak<CompilerLexicalScope>,
    class: CompilerLexicalDeclarationClass,
    name: String,
    visibility: DeclarationVisibility,
    source_context: CompilerSourceContext,
}
impl Display for CompilerLexicalDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let scope_full_name = self.parent.upgrade().map(|x| x.full_scope_display_name()).unwrap_or(String::from("<unknown>"));
        write!(f, "{} {}::{} ({})", self.class, scope_full_name, self.name, self.source_context)
    }
}
impl CompilerLexicalDeclaration {
    fn full_declaration_name(&self) -> String {
        let scope_full_name = self.parent.upgrade().map(|x| x.full_scope_name()).unwrap_or(String::from("<unknown>"));
        format!("{}${}", scope_full_name, self.name.as_str())
    }
}

#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
struct CompilerInstructionRange {
    start_instruction_index: u32,
    end_instruction_index: u32,
}

#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
struct CompilerDebugData {
    block_range: CompilerInstructionRange,
    instruction_line_mappings: HashMap<u32, u32>,
}

#[derive(Debug, Clone, Default)]
struct CompilerLoopCodegenData {
    loop_start_fixups: Vec<GospelJumpLabelFixup>,
    loop_finish_fixups: Vec<GospelJumpLabelFixup>,
}

#[derive(Debug, Clone)]
struct CompilerBlockDeclaration {
    debug_data: Option<CompilerDebugData>,
    loop_codegen_data: Option<CompilerLoopCodegenData>,
}

#[derive(Debug, Clone)]
struct CompilerFunctionDeclaration {
    debug_data: Option<CompilerDebugData>,
    function_reference: CompilerFunctionReference,
}

#[derive(Debug, Clone)]
struct CompilerModuleData {
    visitor: Option<Rc<RefCell<dyn GospelModuleVisitor>>>,
    compiler: Weak<CompilerInstance>,
}

#[derive(Debug, Clone, Display)]
enum CompilerLexicalScopeClass {
    #[strum(to_string = "module")]
    Module(CompilerModuleData),
    #[strum(to_string = "source file")]
    SourceFile(String),
    #[strum(to_string = "namespace")]
    Namespace,
    #[strum(to_string = "function")]
    Function(Rc<RefCell<CompilerFunctionDeclaration>>),
    #[strum(to_string = "block")]
    Block(Rc<RefCell<CompilerBlockDeclaration>>),
}

#[derive(Debug, Clone, Display)]
enum CompilerLexicalNode {
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
    fn node_name(&self) -> &str {
        match &self {
            CompilerLexicalNode::Scope(scope) => scope.name.as_str(),
            CompilerLexicalNode::Declaration(decl) => decl.name.as_str(),
        }
    }
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

#[derive(Debug)]
struct CompilerLexicalScope {
    parent: Option<Weak<CompilerLexicalScope>>,
    class: CompilerLexicalScopeClass,
    name: String,
    visibility: DeclarationVisibility,
    source_context: CompilerSourceContext,
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
    fn create_root_scope(compiler: &Rc<CompilerInstance>, module_name: String, visitor: Option<Rc<RefCell<dyn GospelModuleVisitor>>>, source_context: &CompilerSourceContext) -> Rc<Self> {
        Rc::new(Self{
            parent: None,
            class: CompilerLexicalScopeClass::Module(CompilerModuleData{visitor, compiler: Rc::downgrade(compiler)}),
            name: module_name,
            visibility: DeclarationVisibility::Public,
            source_context: source_context.clone(),
            children: RefCell::new(Vec::new()),
            child_lookup: RefCell::new(HashMap::new()),
            unique_name_counter: RefCell::new(0),
        })
    }
    fn declare_scope_internal(self: &Rc<Self>, name: &str, class: CompilerLexicalScopeClass, visibility: DeclarationVisibility, source_context: &ASTSourceContext) -> CompilerResult<Rc<CompilerLexicalScope>> {
        let file_name_override = if let CompilerLexicalScopeClass::SourceFile(file_name) = &class { Some(file_name.clone()) } else { None };
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
    fn parent_scope(self: &Rc<Self>) -> Option<Rc<Self>> {
        self.parent.as_ref().and_then(|x| x.upgrade())
    }
    fn iterate_scope_chain_inner_first(self: &Rc<Self>) -> impl DoubleEndedIterator<Item = Rc<Self>> {
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
    fn iterate_scope_chain_outer_first(self: &Rc<Self>) -> impl Iterator<Item = Rc<Self>> {
        self.iterate_scope_chain_inner_first().rev()
    }
    fn iterate_children(self: &Rc<Self>) -> impl Iterator<Item = CompilerLexicalNode> {
        self.children.borrow().clone().into_iter()
    }
    fn iterate_children_recursive(self: &Rc<Self>) -> impl Iterator<Item = CompilerLexicalNode> {
        self.iterate_scope_chain_outer_first().flat_map(|x| x.iterate_children().collect::<Vec<CompilerLexicalNode>>())
    }
    fn module_name(self: &Rc<Self>) -> String {
        self.iterate_scope_chain_outer_first()
            .find(|x| matches!(x.class, CompilerLexicalScopeClass::Module(_)))
            .map(|x| x.name.clone()).unwrap()
    }
    fn module_visitor(self: &Rc<Self>) -> Option<Rc<RefCell<dyn GospelModuleVisitor>>> {
        self.iterate_scope_chain_outer_first()
            .find_map(|x| if let CompilerLexicalScopeClass::Module(module) = &x.class { module.visitor.clone() } else { None })
    }
    fn compiler(self: &Rc<Self>) -> Option<Rc<CompilerInstance>> {
        self.iterate_scope_chain_outer_first()
            .find_map(|x| if let CompilerLexicalScopeClass::Module(module) = &x.class { module.compiler.upgrade() } else { None })
    }
    fn file_name(self: &Rc<Self>) -> Option<String> {
        self.source_context.file_name.clone()
    }
    fn is_child_of(self: &Rc<Self>, parent: &Rc<Self>) -> bool {
        let mut current_scope = Some(self.clone());
        while current_scope.is_some() && !Rc::ptr_eq(current_scope.as_ref().unwrap(), parent) {
            current_scope = current_scope.as_ref()
                .and_then(|x| x.parent.as_ref())
                .and_then(|x| x.upgrade());
        }
        current_scope.is_some()
    }
    fn full_scope_name(self: &Rc<Self>) -> String {
        self.iterate_scope_chain_outer_first().skip(1).map(|x| x.name.clone()).join("$")
    }
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
    fn find_unique_child(self: &Rc<Self>, name: &str) -> Option<CompilerLexicalNode> {
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
            } else { Some(child) }
        } else { None }
    }
    fn collect_implicit_scope_parameters(self: &Rc<Self>) -> Vec<Weak<CompilerLexicalDeclaration>> {
        self.iterate_children_recursive().filter_map(|x| {
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


