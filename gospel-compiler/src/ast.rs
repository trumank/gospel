use std::fmt::{Display, Formatter};
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use gospel_typelib::type_model::PrimitiveType;

/// Describes value type of the expression in the source grammar
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Display, Default, EnumString)]
pub enum ExpressionValueType {
    #[default]
    Int,
    Typename,
    Closure,
    MetaStruct,
}

/// Describes a source level access specifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Display)]
pub enum DeclarationAccessSpecifier {
    Local,
    Internal,
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
    StructMakePointer,
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
    pub constant_value: i32,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Display)]
pub enum BuiltinIdentifier {
    AddressSize,
    TargetPlatform,
    TargetArch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuiltinIdentifierExpression {
    pub identifier: BuiltinIdentifier,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveTypeExpression {
    pub primitive_type: PrimitiveType,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}


/// Represents a generic expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression {
    IntegerConstantExpression(Box<IntegerConstantExpression>),
    IdentifierExpression(Box<IdentifierExpression>),
    ConditionalExpression(Box<ConditionalExpression>),
    StructDeclarationExpression(Box<StructStatement>),
    BlockExpression(Box<BlockExpression>),
    UnaryExpression(Box<UnaryExpression>),
    ArrayIndexExpression(Box<ArrayTypeExpression>),
    MemberAccessExpression(Box<MemberAccessExpression>),
    BinaryExpression(Box<BinaryExpression>),
    BuiltinIdentifierExpression(Box<BuiltinIdentifierExpression>),
    PrimitiveTypeExpression(Box<PrimitiveTypeExpression>),
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
pub struct ModuleImportStatement {
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
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a member declaration inside the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberDeclaration {
    pub alignment_expression: Option<Expression>,
    pub member_type_expression: Expression,
    pub name: String,
    pub array_size_expression: Option<Expression>,
    pub bitfield_width_expression: Option<Expression>,
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

/// Represents a declaration in the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StructInnerDeclaration {
    DataDeclaration(Box<DataStatement>),
    NestedStructDeclaration(Box<StructStatement>),
    MemberDeclaration(Box<MemberDeclaration>),
    ConditionalDeclaration(Box<ConditionalDeclaration>),
    BlockDeclaration(Box<BlockDeclaration>),
    EmptyDeclaration,
}

/// Represents a base class declaration for a struct, possibly gated behind a condition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BaseClassDeclaration {
    pub condition_expression: Option<Expression>,
    pub type_expression: Expression,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Declaration of a (potentially templated) struct
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructStatement {
    pub template_declaration: Option<TemplateDeclaration>,
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub alignment_expression: Option<Expression>,
    pub name: Option<String>,
    pub base_class_expressions: Vec<BaseClassDeclaration>,
    pub declarations: Vec<StructInnerDeclaration>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Declaration in a namespace. Namespaces can contain data and struct statements, as well as nested namespaces
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NamespaceLevelDeclaration {
    DataStatement(DataStatement),
    StructStatement(StructStatement),
    EmptyStatement,
    NamespaceStatement(NamespaceStatement),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamespaceStatement {
    pub access_specifier: Option<DeclarationAccessSpecifier>,
    pub name: PartialIdentifier,
    pub declarations: Vec<NamespaceLevelDeclaration>,
    #[serde(default)]
    pub source_context: ASTSourceContext,
}

/// Represents a top level declaration in the module source file
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleTopLevelDeclaration {
    ImportStatement(ModuleImportStatement),
    InputStatement(InputStatement),
    DataStatement(DataStatement),
    StructStatement(StructStatement),
    EmptyStatement,
    NamespaceStatement(NamespaceStatement),
}

/// Represents a source file for a module
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleSourceFile {
    pub file_name: String,
    pub declarations: Vec<ModuleTopLevelDeclaration>,
}
