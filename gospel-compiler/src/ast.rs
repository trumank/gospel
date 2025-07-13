use serde::{Deserialize, Serialize};

/// Describes value type of the expression in the source grammar
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExpressionValueType {
    Int,
    Typename,
    Template,
}

/// Partial or fully qualified name in source code
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct PartialIdentifier {
    pub path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArrayIndexExpression {
    pub array_expression: Expression,
    pub index_expression: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemplateInstantiationExpression {
    pub template_name: PartialIdentifier,
    pub argument_expressions: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicTemplateInstantiationExpression {
    pub template_pointer_expression: Expression,
    pub argument_expressions: Vec<Expression>,
}

/// Inline struct declaration expression. Has more restrictions than struct statements:
/// it cannot have an alignment operator, base classes, or name, it is always an unnamed struct with default alignment and no parent classes
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructDeclarationExpression {
    pub declarations: Vec<StructInnerDeclaration>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalExpression {
    pub condition_expression: Expression,
    pub true_expression: Expression,
    pub false_expression: Expression,
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
    LogicalAnd,
    LogicalOr,
    Equals,
    NotEquals,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryExpression {
    pub left_expression: Expression,
    pub operator: BinaryOperator,
    pub right_expression: Expression,
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
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberAccessExpression {
    pub type_expression: Expression,
    pub member_type: ExpressionValueType,
    pub member_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssignmentStatement {
    pub left_hand_expression: Expression,
    pub assignment_operator: Option<BinaryOperator>,
    pub assignment_expression: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalStatement {
    pub condition_expression: Expression,
    pub then_statement: Statement,
    pub else_statement: Option<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockStatement {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalVarDeclarationStatement {
    pub value_type: ExpressionValueType,
    pub name: String,
    pub initializer: Option<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WhileLoopStatement {
    pub condition_expression: Expression,
    pub loop_body_statement: Statement,
}

/// Represents a generic statement inside an expression block
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement {
    BlockStatement(Box<BlockStatement>),
    ConditionalStatement(Box<ConditionalStatement>),
    AssignmentStatement(Box<AssignmentStatement>),
    DeclarationStatement(Box<LocalVarDeclarationStatement>),
    WhileLoopStatement(Box<WhileLoopStatement>),
    BreakLoopStatement,
    ContinueLoopStatement,
    EmptyStatement,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockExpression {
    pub statements: Vec<Statement>,
    pub return_value_expression: Expression,
}

/// Represents a generic expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression {
    IntegerConstantExpression(i32),
    TemplatePointerConstantExpression(PartialIdentifier),
    IdentifierExpression(PartialIdentifier),
    TemplateInstantiationExpression(Box<TemplateInstantiationExpression>),
    TemplateInstantiationByPointerExpression(Box<DynamicTemplateInstantiationExpression>),
    ConditionalExpression(Box<ConditionalExpression>),
    StructDeclarationExpression(Box<StructDeclarationExpression>),
    BlockExpression(Box<BlockExpression>),
    UnaryExpression(Box<UnaryExpression>),
    ArrayIndexExpression(Box<ArrayIndexExpression>),
    MemberAccessExpression(Box<MemberAccessExpression>),
    BinaryExpression(Box<BinaryExpression>),
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ModuleCompositeImport {
    pub namespace: PartialIdentifier,
    pub imported_names: Vec<String>,
}

/// Represents an import statement in its possible forms
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleImportStatement {
    QualifiedImport(PartialIdentifier),
    NamespaceImport(PartialIdentifier),
    CompositeImport(ModuleCompositeImport),
}

/// Represents an external data declaration
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternStatement {
    pub global_name: String,
    pub value_type: ExpressionValueType,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemplateArgument {
    pub name: String,
    pub value_type: ExpressionValueType,
    pub default_value: Option<Expression>,
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
    pub value_type: ExpressionValueType,
    pub name: String,
    pub initializer: Expression,
}

/// Represents a member declaration inside the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberDeclaration {
    pub alignment_expression: Option<Expression>,
    pub member_type_expression: Expression,
    pub name: String,
    pub array_size_expression: Option<Expression>,
    pub bitfield_width_expression: Option<Expression>,
}

/// Represents a conditional declaration inside the struct definition
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConditionalDeclaration {
    pub condition_expression: Expression,
    pub then_branch: StructInnerDeclaration,
    pub else_branch: Option<StructInnerDeclaration>,
}

/// Represents a group of struct declarations grouped into a single logical block
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockDeclaration {
    pub declarations: Vec<StructInnerDeclaration>,
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

/// Declaration of a (potentially templated) struct
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructStatement {
    pub template_declaration: Option<TemplateDeclaration>,
    pub alignment_expression: Option<Expression>,
    pub name: String,
    pub base_class_expressions: Vec<Expression>,
    pub declarations: Vec<StructInnerDeclaration>,
}

/// Represents a top level declaration in the module source file
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleTopLevelDeclaration {
    ImportStatement(ModuleImportStatement),
    ExternStatement(ExternStatement),
    DataStatement(DataStatement),
    StructStatement(StructStatement),
    EmptyStatement,
}

/// Represents a source file for a module
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleSourceFile {
    pub declarations: Vec<ModuleTopLevelDeclaration>,
}
