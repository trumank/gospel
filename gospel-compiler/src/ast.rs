use std::fmt::{Display, Formatter};
use std::iter::{empty, once};
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use gospel_typelib::type_model::{EnumKind, PrimitiveType, UserDefinedTypeKind, IntegralType};

/// Describes value type of the expression in the source grammar
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, EnumString)]
pub enum ExpressionValueType {
    Any,
    Integer(IntegralType),
    Typename,
    Bool,
    Closure,
    MetaStruct,
}
impl Default for ExpressionValueType {
    fn default() -> Self {
        ExpressionValueType::Integer(IntegralType::default())
    }
}

/// Describes a source level access specifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Display)]
pub enum DeclarationAccessSpecifier {
    /// Visible to the other declarations within the same source code file
    Local,
    /// Visible to other declarations within the same module
    Internal,
    /// Visible to other declarations across all modules
    Public,
}

/// Represents a type of partial identifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Display)]
pub enum PartialIdentifierKind {
    Absolute,
    ModuleRelative,
    Relative,
}

/// Partial or fully qualified name in source code
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PartialIdentifier {
    pub kind: PartialIdentifierKind,
    pub path: Vec<String>,
}

/// Describes a location of the declaration within the source file
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ASTSourceContext {
    pub line_number: usize,
    pub line_offset: usize,
}
impl Display for ASTSourceContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line_number, self.line_offset)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArrayTypeExpression {
    pub element_type_expression: Expression,
    pub array_length_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalExpression {
    pub condition_expression: Expression,
    pub true_expression: Expression,
    pub false_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOperator {
    BitwiseOr,
    BitwiseAnd,
    BitwiseXor,
    BitwiseShiftLeft,
    BitwiseShiftRight,
    ArithmeticAdd,
    ArithmeticSubtract,
    ArithmeticMultiply,
    ArithmeticDivide,
    ArithmeticRemainder,
    LogicalLess,
    LogicalMore,
    LogicalLessEquals,
    LogicalMoreEquals,
    ShortCircuitAnd,
    ShortCircuitOr,
    Equals,
    NotEquals,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryExpression {
    pub left_expression: Expression,
    pub operator: BinaryOperator,
    pub right_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOperator {
    CreatePointerType,
    CreateReferenceType,
    StructSizeOf,
    StructAlignOf,
    BitwiseInverse,
    ArithmeticNegate,
    BoolNegate,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberAccessExpression {
    pub type_expression: Expression,
    pub member_type: ExpressionValueType,
    pub member_name: String,
    pub template_arguments: Option<Vec<Expression>>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssignmentStatement {
    pub left_hand_expression: Expression,
    pub assignment_operator: Option<BinaryOperator>,
    pub assignment_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalStatement {
    pub condition_expression: Expression,
    pub then_statement: Statement,
    pub else_statement: Option<Statement>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockStatement {
    pub statements: Vec<Statement>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclarationStatement {
    pub value_type: ExpressionValueType,
    pub name: String,
    pub initializer: Option<Expression>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WhileLoopStatement {
    pub condition_expression: Expression,
    pub loop_body_statement: Statement,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimpleStatement {
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a generic statement inside an expression block
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement {
    BlockStatement(Box<BlockStatement>),
    ConditionalStatement(Box<ConditionalStatement>),
    AssignmentStatement(Box<AssignmentStatement>),
    DeclarationStatement(Box<DeclarationStatement>),
    WhileLoopStatement(Box<WhileLoopStatement>),
    BreakLoopStatement(Box<SimpleStatement>),
    ContinueLoopStatement(Box<SimpleStatement>),
    EmptyStatement(Box<SimpleStatement>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockExpression {
    pub statements: Vec<Statement>,
    pub return_value_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentifierExpression {
    pub identifier: PartialIdentifier,
    pub template_arguments: Option<Vec<Expression>>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegerConstantExpression {
    /// Converted to unsigned type and zero-extended to 64-bit
    pub raw_constant_value: u64,
    pub constant_type: IntegralType,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoolConstantExpression {
    pub bool_value: bool,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerBuiltinExpression {
    pub identifier: String,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveTypeExpression {
    pub primitive_type: PrimitiveType,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CVQualifiedExpression {
    pub base_expression: Expression,
    pub constant: bool,
    pub volatile: bool,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StaticCastExpression {
    pub cast_expression: Expression,
    pub target_type: ExpressionValueType,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwitchExpressionCase {
    pub match_expression: Expression,
    pub result_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwitchExpressionDefaultCase {
    pub result_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwitchExpression {
    pub target_expression: Expression,
    pub switch_cases: Vec<SwitchExpressionCase>,
    pub default_case: Option<SwitchExpressionDefaultCase>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionPointerExpression {
    pub return_value_type: Expression,
    pub receiver_type: Option<Expression>,
    pub argument_types: Vec<Expression>,
    pub constant: bool,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a generic expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression {
    IntegerConstantExpression(Box<IntegerConstantExpression>),
    BoolConstantExpression(Box<BoolConstantExpression>),
    IdentifierExpression(Box<IdentifierExpression>),
    ConditionalExpression(Box<ConditionalExpression>),
    StructDeclarationExpression(Box<StructStatement>),
    BlockExpression(Box<BlockExpression>),
    UnaryExpression(Box<UnaryExpression>),
    ArrayIndexExpression(Box<ArrayTypeExpression>),
    MemberAccessExpression(Box<MemberAccessExpression>),
    BinaryExpression(Box<BinaryExpression>),
    CompilerBuiltinExpression(Box<CompilerBuiltinExpression>),
    PrimitiveTypeExpression(Box<PrimitiveTypeExpression>),
    CVQualifiedExpression(Box<CVQualifiedExpression>),
    StaticCastExpression(Box<StaticCastExpression>),
    SwitchExpression(Box<SwitchExpression>),
    FunctionPointerExpression(Box<FunctionPointerExpression>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleCompositeImport {
    pub namespace: PartialIdentifier,
    pub imported_names: Vec<String>,
}

/// Represents an import statement in its possible forms
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleImportStatementType {
    QualifiedImport(PartialIdentifier),
    CompositeImport(ModuleCompositeImport),
}

/// Represents an import statement
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImportStatement {
    pub statement_type: ModuleImportStatementType,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents an input data declaration with an optional default value expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InputStatement {
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub global_name: String,
    pub value_type: ExpressionValueType,
    pub default_value: Option<Expression>,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemplateArgument {
    pub name: String,
    pub value_type: ExpressionValueType,
    pub default_value: Option<Expression>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Declaration of data or type template with names of arguments and their types
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TemplateDeclaration {
    pub arguments: Vec<TemplateArgument>,
}

/// Declaration of a data or a type alias using the specified initializer expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataStatement {
    pub template_declaration: Option<TemplateDeclaration>,
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub value_type: ExpressionValueType,
    pub name: String,
    pub initializer: Expression,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a member declaration inside the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberDeclaration {
    pub alignment_expression: Option<ExpressionWithCondition>,
    pub member_type_expression: Expression,
    pub name: Option<String>,
    pub array_size_expression: Option<Expression>,
    pub bitfield_width_expression: Option<Expression>,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a conditional declaration inside the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalDeclaration {
    pub condition_expression: Expression,
    pub then_branch: StructInnerDeclaration,
    pub else_branch: Option<StructInnerDeclaration>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a group of struct declarations grouped into a single logical block
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockDeclaration {
    pub declarations: Vec<StructInnerDeclaration>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionParameterDeclaration {
    pub parameter_type: Expression,
    pub parameter_name: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a virtual function declaration
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberFunctionDeclaration {
    pub name: String,
    pub return_value_type: Expression,
    pub parameters: Vec<FunctionParameterDeclaration>,
    pub constant: bool,
    pub is_override: bool,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a declaration in the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StructInnerDeclaration {
    DataDeclaration(Box<DataStatement>),
    NestedStructDeclaration(Box<StructStatement>),
    MemberDeclaration(Box<MemberDeclaration>),
    ConditionalDeclaration(Box<ConditionalDeclaration>),
    BlockDeclaration(Box<BlockDeclaration>),
    FunctionDeclaration(Box<MemberFunctionDeclaration>),
    EmptyDeclaration,
}
impl StructInnerDeclaration {
    /// Iterates this inner declaration and all of its children declarations. This will NOT recurse into nested struct declaration members
    pub fn iterate_recursive<'a>(&'a self) -> Box<dyn Iterator<Item = &'a StructInnerDeclaration> + 'a> {
        match self {
            StructInnerDeclaration::BlockDeclaration(block_declaration) => {
                Box::new(once(self)
                    .chain(block_declaration.declarations.iter().flat_map(|x| x.iterate_recursive())))
            }
            StructInnerDeclaration::ConditionalDeclaration(conditional_declaration) => {
                Box::new(once(self)
                    .chain(conditional_declaration.then_branch.iterate_recursive())
                    .chain(conditional_declaration.else_branch.as_ref().map(|x| x.iterate_recursive()).unwrap_or(Box::new(empty()))))
            }
            _ => {
                Box::new(once(self))
            },
        }
    }
}

/// Represents a declaration for a struct that might be gated behind a condition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpressionWithCondition {
    pub condition_expression: Option<Expression>,
    pub expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Declaration of a (potentially templated) struct
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructStatement {
    pub template_declaration: Option<TemplateDeclaration>,
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub struct_kind: UserDefinedTypeKind,
    pub alignment_expression: Option<ExpressionWithCondition>,
    pub member_pack_expression: Option<ExpressionWithCondition>,
    pub name: Option<String>,
    pub base_class_expressions: Vec<ExpressionWithCondition>,
    pub declarations: Vec<StructInnerDeclaration>,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a declaration of a single constant inside an enum
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnumConstantDeclaration {
    pub condition_expression: Option<Expression>,
    pub name: Option<String>,
    pub value_expression: Option<Expression>,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a declaration of an enumeration type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnumStatement {
    pub template_declaration: Option<TemplateDeclaration>,
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub enum_kind: EnumKind,
    pub underlying_type_expression: Option<ExpressionWithCondition>,
    pub name: Option<String>,
    pub constants: Vec<EnumConstantDeclaration>,
    pub doc_comment: Option<String>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Declaration in a namespace or top level scope in a source file
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TopLevelDeclaration {
    ImportStatement(ImportStatement),
    InputStatement(InputStatement),
    DataStatement(DataStatement),
    StructStatement(StructStatement),
    EnumStatement(EnumStatement),
    EmptyStatement,
    NamespaceStatement(NamespaceStatement),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamespaceStatement {
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub name: PartialIdentifier,
    pub declarations: Vec<TopLevelDeclaration>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a source file for a module
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleSourceFile {
    pub file_name: String,
    pub declarations: Vec<TopLevelDeclaration>,
}
