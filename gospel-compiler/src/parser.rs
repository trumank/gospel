use crate::ast::{ASTSourceContext, ArrayTypeExpression, AssignmentStatement, BinaryExpression, BinaryOperator, BlockDeclaration, BlockExpression, BlockStatement, ConditionalDeclaration, ConditionalExpression, ConditionalStatement, DataStatement, Expression, ExpressionValueType, InputStatement, DeclarationStatement, MemberAccessExpression, MemberDeclaration, ModuleCompositeImport, ModuleImportStatement, ModuleImportStatementType, ModuleSourceFile, ModuleTopLevelDeclaration, NamespaceLevelDeclaration, NamespaceStatement, PartialIdentifier, PartialIdentifierKind, Statement, StructInnerDeclaration, StructStatement, TemplateArgument, TemplateDeclaration, UnaryExpression, UnaryOperator, WhileLoopStatement, SimpleStatement, IdentifierExpression, IntegerConstantExpression, BuiltinIdentifier, BuiltinIdentifierExpression, DeclarationAccessSpecifier, PrimitiveTypeExpression, CVQualifiedExpression};
use crate::lex_util::get_line_number_and_offset_from_index;
use anyhow::{anyhow, bail};
use logos::{Lexer, Logos};
use std::fmt::{Display, Formatter};
use strum::Display;
use fancy_regex::{Captures, Regex};
use crate::ast::BaseClassDeclaration;
use gospel_typelib::type_model::{PrimitiveType, UserDefinedTypeKind};

#[derive(Logos, Debug, Clone, PartialEq, Display)]
#[logos(skip r"[ \r\t\n\u{feff}]+")]
enum CompilerToken {
    #[token("import")]
    #[strum(to_string = "import")]
    Import,
    #[token("input")]
    #[strum(to_string = "input")]
    Input,
    #[token("template")]
    #[strum(to_string = "template")]
    Template,
    #[token("type")]
    #[strum(to_string = "type")]
    Type,
    #[token("struct")]
    #[strum(to_string = "struct")]
    Struct,
    #[token("class")]
    #[strum(to_string = "class")]
    Class,
    #[token("union")]
    #[strum(to_string = "union")]
    Union,
    #[token("constexpr")]
    #[strum(to_string = "constexpr")]
    Constexpr,
    #[token("const")]
    #[strum(to_string = "const")]
    Const,
    #[token("volatile")]
    #[strum(to_string = "volatile")]
    Volatile,
    #[token("let")]
    #[strum(to_string = "let")]
    Let,
    #[token("typename")]
    #[strum(to_string = "typename")]
    Typename,
    #[token("<")]
    #[strum(to_string = "<")]
    LessOrArgumentListStart,
    #[token(">")]
    #[strum(to_string = ">")]
    MoreOrArgumentListEnd,
    #[token("if")]
    #[strum(to_string = "if")]
    If,
    #[token("else")]
    #[strum(to_string = "else")]
    Else,
    #[token("while")]
    #[strum(to_string = "while")]
    While,
    #[token("break")]
    #[strum(to_string = "break")]
    Break,
    #[token("continue")]
    #[strum(to_string = "continue")]
    Continue,
    #[token("=")]
    #[strum(to_string = "=")]
    Assignment,
    #[token("&")]
    #[strum(to_string = "&")]
    BitwiseAnd,
    #[token("*")]
    #[strum(to_string = "*")]
    PointerOrMultiply,
    #[token("sizeof")]
    #[strum(to_string = "sizeof")]
    Sizeof,
    #[token("alignof")]
    #[strum(to_string = "alignof")]
    Alignof,
    #[token("alignas")]
    #[strum(to_string = "alignas")]
    Alignas,
    #[token("namespace")]
    #[strum(to_string = "namespace")]
    Namespace,
    #[token("module")]
    #[strum(to_string = "module")]
    Module,
    #[token("public")]
    #[strum(to_string = "public")]
    Public,
    #[token("internal")]
    #[strum(to_string = "internal")]
    Internal,
    #[token("local")]
    #[strum(to_string = "local")]
    Local,
    #[token("__address_size")]
    #[strum(to_string = "__address_size")]
    BuiltinAddressSize,
    #[token("__target_platform")]
    #[strum(to_string = "__target_platform")]
    BuiltinTargetPlatform,
    #[token("__target_arch")]
    #[strum(to_string = "__target_arch")]
    BuiltinTargetArch,
    #[token("void")]
    #[strum(to_string = "void")]
    PrimitiveTypeVoid,
    #[token("char")]
    #[strum(to_string = "char")]
    PrimitiveTypeChar,
    #[token("wchar_t")]
    #[strum(to_string = "wchar_t")]
    PrimitiveTypeWideChar,
    #[token("int")]
    #[strum(to_string = "int")]
    PrimitiveTypeInt,
    #[token("float")]
    #[strum(to_string = "float")]
    PrimitiveTypeFloat,
    #[token("double")]
    #[strum(to_string = "double")]
    PrimitiveTypeDouble,
    #[token("bool")]
    #[strum(to_string = "bool")]
    PrimitiveTypeBool,
    #[token("char8_t")]
    #[strum(to_string = "char8_t")]
    PrimitiveTypeChar8,
    #[token("char16_t")]
    #[strum(to_string = "char16_t")]
    PrimitiveTypeChar16,
    #[token("char32_t")]
    #[strum(to_string = "char32_t")]
    PrimitiveTypeChar32,
    #[token("unsigned")]
    #[strum(to_string = "unsigned")]
    PrimitiveModifierUnsigned,
    #[token("long")]
    #[strum(to_string = "long")]
    PrimitiveModifierLong,
    #[token("short")]
    #[strum(to_string = "short")]
    PrimitiveModifierShort,
    #[token("~")]
    #[strum(to_string = "~")]
    BitwiseInverse,
    #[token("-")]
    #[strum(to_string = "-")]
    NegateOrSubtract,
    #[token("!")]
    #[strum(to_string = "!")]
    BoolNegate,
    #[token("|")]
    #[strum(to_string = "|")]
    BitwiseOr,
    #[token("^")]
    #[strum(to_string = "^")]
    BitwiseXor,
    #[token("<<")]
    #[strum(to_string = "<<")]
    BitwiseShiftLeft,
    #[token("+")]
    #[strum(to_string = "+")]
    Add,
    #[token("/")]
    #[strum(to_string = "/")]
    Divide,
    #[token("%")]
    #[strum(to_string = "%")]
    Remainder,
    #[token("<=")]
    #[strum(to_string = "<=")]
    LessEquals,
    #[token(">=")]
    #[strum(to_string = ">=")]
    MoreEquals,
    #[token("&&")]
    #[strum(to_string = "&&")]
    And,
    #[token("||")]
    #[strum(to_string = "||")]
    Or,
    #[token("==")]
    #[strum(to_string = "==")]
    Equals,
    #[token("!=")]
    #[strum(to_string = "!=")]
    NotEquals,
    #[token("|=")]
    #[strum(to_string = "|=")]
    BitwiseOrAssignment,
    #[token("&=")]
    #[strum(to_string = "&=")]
    BitwiseAndAssignment,
    #[token("+=")]
    #[strum(to_string = "+=")]
    AddAssignment,
    #[token("-=")]
    #[strum(to_string = "-=")]
    SubtractAssignment,
    #[token("*=")]
    #[strum(to_string = "*=")]
    MultiplyAssignment,
    #[token("/=")]
    #[strum(to_string = "/=")]
    DivideAssignment,
    #[token("{")]
    #[strum(to_string = "{")]
    ScopeStart,
    #[token("}")]
    #[strum(to_string = "}}")]
    ScopeEnd,
    #[token("(")]
    #[strum(to_string = "(")]
    SubExpressionStart,
    #[token(")")]
    #[strum(to_string = ")")]
    SubExpressionEnd,
    #[token("[")]
    #[strum(to_string = "[")]
    ArraySubscriptStart,
    #[token("]")]
    #[strum(to_string = "]")]
    ArraySubscriptEnd,
    #[token(";")]
    #[strum(to_string = ";")]
    Terminator,
    #[token("::")]
    #[strum(to_string = "::")]
    ScopeDelimiter,
    #[token(":")]
    #[strum(to_string = ":")]
    BaseClass,
    #[token(",")]
    #[strum(to_string = ",")]
    Separator,
    // Identifiers and literals
    #[regex("[A-Za-z_$][A-Za-z0-9_$]*", parse_identifier)]
    #[strum(to_string = "identifier")]
    Identifier(String),
    #[regex("-?(?:0x[A-Fa-f0-9]+)|(?:0b[0-1]+)|(?:(?:[1-9]+[0-9]*)|0)", parse_integer_literal)]
    #[strum(to_string = "integer literal")]
    IntegerLiteral(i32),
}
fn parse_identifier(lex: &mut Lexer<CompilerToken>) -> Option<String> {
    let identifier_slice = lex.slice();
    Some(identifier_slice.to_string())
}
fn parse_integer_literal(lex: &mut Lexer<CompilerToken>) -> Option<i32> {
    let mut string_slice: &str = lex.slice();
    let mut sign_multiplier = 1;
    if string_slice.starts_with('-') {
        string_slice = &string_slice[1..];
        sign_multiplier = -1;
    }
    if string_slice.starts_with("0x") {
        string_slice = &string_slice[2..];
        i32::from_str_radix(string_slice, 16).ok().map(|x| x * sign_multiplier)
    } else if string_slice.starts_with("0b") {
        string_slice = &string_slice[2..];
        i32::from_str_radix(string_slice, 2).ok().map(|x| x * sign_multiplier)
    } else {
        i32::from_str_radix(string_slice, 10).ok().map(|x| x * sign_multiplier)
    }
}

#[derive(Debug, Clone)]
struct CompilerLexerContext<'a> {
    file_name: &'a str,
    lex: Lexer<'a, CompilerToken>,
    buffered_next_token: Option<Option<CompilerToken>>,
}
impl CompilerLexerContext<'_> {
    fn context_str(&self) -> String {
        let start_offset = self.lex.span().start;
        let (line_number, line_offset) = get_line_number_and_offset_from_index(self.lex.source(), start_offset);
        let file_name = self.file_name.to_string();
        format!("(file: {} line {} offset {})", file_name, line_number + 1, line_offset)
    }
    fn source_context(&self) -> ASTSourceContext {
        let start_offset = self.lex.span().start;
        let (line_number, line_offset) = get_line_number_and_offset_from_index(self.lex.source(), start_offset);
        ASTSourceContext{ line_number: line_number + 1, line_offset }
    }
    fn fail<T: AsRef<str>>(&self, error: T) -> anyhow::Error {
        anyhow!("{} {}", error.as_ref(), self.context_str())
    }
    fn peek_or_eof(&mut self) -> anyhow::Result<Option<CompilerToken>> {
        if let Some(next_token) = &self.buffered_next_token {
            Ok(next_token.clone())
        } else {
            let new_buffered_next_token = match self.lex.next() {
                Some(wrapped_token) => match wrapped_token {
                    Ok(result) => Some(result),
                    Err(_) => { return Err(self.fail("Failed to parse next token")); }
                },
                None => None
            };
            self.buffered_next_token = Some(new_buffered_next_token.clone());
            Ok(new_buffered_next_token)
        }
    }
    fn next_or_eof(&mut self) -> anyhow::Result<Option<CompilerToken>> {
        if let Some(next_token) = self.buffered_next_token.take() {
            Ok(next_token)
        } else if let Some(wrapped_token) = self.lex.next() {
            match wrapped_token {
                Ok(result) => Ok(Some(result)),
                Err(_) => Err(self.fail("Failed to parse next token"))
            }
        } else { Ok(None) }
    }
    fn peek(&mut self) -> anyhow::Result<CompilerToken> {
        self.peek_or_eof()?.ok_or_else(|| self.fail("Expected a token, received <EOF>"))
    }
    fn next(&mut self) -> anyhow::Result<CompilerToken> {
        self.next_or_eof()?.ok_or_else(|| self.fail("Expected a token, received <EOF>"))
    }
    fn discard_next(&mut self) -> anyhow::Result<()> {
        self.next()?;
        Ok({})
    }

    fn check_token(&mut self, token: CompilerToken, expected: CompilerToken) -> anyhow::Result<()> {
        if token != expected {
            Err(self.fail(format!("Expected {}, got {}", expected, token)))
        } else { Ok({}) }
    }
    fn check_identifier(&mut self, token: CompilerToken) -> anyhow::Result<String> {
        match token {
            CompilerToken::Identifier(value) => Ok(value),
            other => Err(self.fail(format!("Expected identifier, got {}", other)))
        }
    }
}

#[derive(Clone)]
struct ExactParseCase<'a, T : Clone> {
    parser: CompilerParserInstance<'a>,
    data: T,
}
impl<'a, T : Clone> ExactParseCase<'a, T> {
    fn create(parser: CompilerParserInstance<'a>, data: T) -> ExactParseCase<'a, T> {
        ExactParseCase{ parser, data }
    }
    fn map_data<O: Clone, S: FnOnce(T) -> O>(self, mapper: S) -> ExactParseCase<'a, O> {
        ExactParseCase{ parser: self.parser, data: mapper(self.data) }
    }
    fn map_result<O, S: FnOnce(CompilerParserInstance<'a>, T) -> anyhow::Result<O>>(self, mapper: S) -> anyhow::Result<O> {
        mapper(self.parser, self.data)
    }
    fn repeat(self, num_cases: usize) -> AmbiguousParsingResult<'a, (T, usize)> {
        let mut result_cases: Vec<ExactParseCase<'a, (T, usize)>> = Vec::new();
        for index in 0..num_cases {
            result_cases.push(ExactParseCase{ parser: self.parser.clone(), data: (self.data.clone(), index) })
        }
        AmbiguousParsingResult::<'a, (T, usize)>::from_cases(result_cases)
    }
    fn to_parse_result(self) -> AmbiguousParsingResult<'a, T> {
        AmbiguousParsingResult::from_cases(vec![self])
    }
}

#[derive(Clone)]
struct AmbiguousParsingResult<'a, T : Clone> {
    cases: Vec<ExactParseCase<'a, T>>
}
impl<'a, T : Clone> AmbiguousParsingResult<'a, T> {
    fn unambiguous(parser: CompilerParserInstance<'a>, data: T) -> Self {
        Self { cases: vec![ExactParseCase { parser, data }] }
    }
    fn from_cases(cases: Vec<ExactParseCase<'a, T>>) -> Self {
        Self { cases }
    }
    fn checked_from_cases(cases: Vec<ExactParseCase<'a, T>>, errored_cases: Vec<anyhow::Error>) -> anyhow::Result<Self> {
        if cases.is_empty() {
            if errored_cases.len() == 1 {
                Err(anyhow!("{}", errored_cases[0].to_string()))
            } else {
                let joined_error_messages: Vec<String> = errored_cases.iter().map(|x| x.to_string()).collect();
                Err(anyhow!("Could not deduce valid grammar, all cases are invalid: {}", joined_error_messages.join(" (and) ")))
            }
        } else { Ok(AmbiguousParsingResult::from_cases(cases)) }
    }
    fn map_data<O : Clone, S: Fn(T) -> O>(self, mapper: S) -> AmbiguousParsingResult<'a, O> {
        let mut result_cases: Vec<ExactParseCase<'a, O>> = Vec::with_capacity(self.cases.len());
        for original_case in self.cases {
            let result_data = mapper(original_case.data);
            result_cases.push(ExactParseCase{ parser: original_case.parser, data: result_data });
        }
        AmbiguousParsingResult::<'a, O>::from_cases(result_cases)
    }
    fn flat_map_result<O : Clone, S: Fn(CompilerParserInstance<'a>, T) -> anyhow::Result<AmbiguousParsingResult<'a, O>>>(self, mapper: S) -> anyhow::Result<AmbiguousParsingResult<'a, O>> {
        let mut result_cases: Vec<ExactParseCase<'a, O>> = Vec::with_capacity(self.cases.len());
        let mut errored_cases: Vec<anyhow::Error> = Vec::new();
        for original_case in self.cases {
            match mapper(original_case.parser, original_case.data) {
                Ok(mut ambiguous_result) => result_cases.append(&mut ambiguous_result.cases),
                Err(error) => errored_cases.push(error),
            }
        }
        AmbiguousParsingResult::<'a, O>::checked_from_cases(result_cases, errored_cases)
    }
    fn disambiguate_generic<S: Fn(&T) -> String>(mut self, to_string: S) -> anyhow::Result<ExactParseCase<'a, T>> {
        if self.cases.len() != 1 {
            let context_message = self.cases[0].parser.ctx.context_str();
            let error_messages: Vec<String> = self.cases.iter_mut().map(|x| to_string(&x.data)).collect();
            Err(anyhow!("Ambiguous source text {}\ncould be {}", context_message, error_messages.join("\nor ")))
        } else {
            Ok(self.cases.pop().unwrap())
        }
    }
}
impl<'a, T : Clone + ToString> AmbiguousParsingResult<'a, T> {
    fn disambiguate(self) -> anyhow::Result<ExactParseCase<'a, T>> {
        self.disambiguate_generic(|x| x.to_string())
    }
}

type AmbiguousExpression<'a> = AmbiguousParsingResult<'a, Expression>;
type ExactExpressionCase<'a> = ExactParseCase<'a, Expression>;
type ExactStatementCase<'a> = ExactParseCase<'a, Statement>;
type ExactStructInnerDeclarationCase<'a> = ExactParseCase<'a, StructInnerDeclaration>;
type ExactModuleTopLevelDeclarationCase<'a> = ExactParseCase<'a, ModuleTopLevelDeclaration>;
type ExactNamespaceLevelDeclarationCase<'a> = ExactParseCase<'a, NamespaceLevelDeclaration>;

#[derive(Clone, PartialEq, Eq)]
enum AssociativeExpressionGroupOperand {
    Expression(Expression),
    Operator((BinaryOperator, ASTSourceContext)),
}

#[derive(Debug, Clone)]
struct CompilerParserInstance<'a> {
    ctx: CompilerLexerContext<'a>,
}
impl<'a> CompilerParserInstance<'a> {
    fn preprocess_input_text(input: &str) -> anyhow::Result<String> {
        let comment_regex = Regex::new(r#"/\*(?:(?!\*/)[\S\s])*\*/|//.*"#).map_err(|x| anyhow!(x.to_string()))?;
        Ok(comment_regex.replace_all(input, |captures: &Captures| -> String {
            // We cannot simply replace comments with empty string because that would shift the line numbers and offsets, so we preserve the character subset ignored by the parser and replace everything else with whitespaces
            captures.get(0).unwrap().as_str().chars().map(|char| if char == '\r' || char == '\t' || char == '\n' || char == '\u{feff}' { char } else { ' ' }).collect()
        }).to_string())
    }
    fn take_parse_case(self) -> ExactParseCase<'a, ()> {
        ExactParseCase{ parser: self, data: () }
    }
    fn parse_expression_value_type(&mut self, token: CompilerToken) -> anyhow::Result<ExpressionValueType> {
        match token {
            CompilerToken::PrimitiveTypeInt => Ok(ExpressionValueType::Int),
            CompilerToken::Typename => Ok(ExpressionValueType::Typename),
            _ => Err(self.ctx.fail(format!("Expected int or typename, got {}", token))),
        }
    }
    fn parse_partial_identifier(&mut self) -> anyhow::Result<PartialIdentifier> {
        let first_identifier_token = self.ctx.peek()?;
        let identifier_type = if first_identifier_token == CompilerToken::Module {
            self.ctx.discard_next()?;
            let scope_separator_token = self.ctx.next()?;
            self.ctx.check_token(scope_separator_token, CompilerToken::ScopeDelimiter)?;
            PartialIdentifierKind::ModuleRelative
        } else if first_identifier_token == CompilerToken::ScopeDelimiter {
            self.ctx.discard_next()?;
            PartialIdentifierKind::Absolute
        } else { PartialIdentifierKind::Relative };

        let mut result = PartialIdentifier{kind: identifier_type, path: Vec::new()};

        // We need to look one token ahead, so we need to fork a parser here
        let mut lookahead_parser = self.clone();
        loop {
            let current_token = self.ctx.next()?;
            lookahead_parser.ctx.discard_next()?;

            let identifier = self.ctx.check_identifier(current_token)?;
            result.path.push(identifier);

            // Check if we have a namespace separator followed by identifier next. We have to use a lookahead parser because namespace separator is ambiguous with member access operator (A::B vs A::struct B)
            let next_namespace_token = lookahead_parser.ctx.next_or_eof()?;
            let next_identifier_token = lookahead_parser.ctx.peek_or_eof()?;
            if next_namespace_token != Some(CompilerToken::ScopeDelimiter) || !next_identifier_token.is_some() || lookahead_parser.ctx.check_identifier(next_identifier_token.unwrap()).is_err()  {
                break;
            }
            self.ctx.discard_next()?;
        }
        Ok(result)
    }
    fn try_parse_binary_operator(token: CompilerToken) -> Option<(BinaryOperator, bool)> {
        match token {
            CompilerToken::BitwiseOr => Some((BinaryOperator::BitwiseOr, false)),
            CompilerToken::BitwiseAnd => Some((BinaryOperator::BitwiseAnd, false)),
            CompilerToken::BitwiseXor => Some((BinaryOperator::BitwiseXor, false)),
            CompilerToken::BitwiseShiftLeft => Some((BinaryOperator::BitwiseShiftLeft, false)),
            CompilerToken::Add => Some((BinaryOperator::ArithmeticAdd, false)),
            CompilerToken::NegateOrSubtract => Some((BinaryOperator::ArithmeticSubtract, true)),
            CompilerToken::PointerOrMultiply => Some((BinaryOperator::ArithmeticMultiply, true)),
            CompilerToken::Divide => Some((BinaryOperator::ArithmeticDivide, false)),
            CompilerToken::Remainder => Some((BinaryOperator::ArithmeticRemainder, false)),
            CompilerToken::LessOrArgumentListStart => Some((BinaryOperator::LogicalLess, true)),
            CompilerToken::MoreOrArgumentListEnd => Some((BinaryOperator::LogicalMore, true)),
            CompilerToken::LessEquals => Some((BinaryOperator::LogicalLessEquals, false)),
            CompilerToken::MoreEquals => Some((BinaryOperator::LogicalMoreEquals, true)),
            CompilerToken::And => Some((BinaryOperator::ShortCircuitAnd, false)),
            CompilerToken::Or => Some((BinaryOperator::ShortCircuitOr, false)),
            CompilerToken::Equals => Some((BinaryOperator::Equals, false)),
            CompilerToken::NotEquals => Some((BinaryOperator::NotEquals, false)),
            _ => None,
        }
    }
    fn try_parse_assignment_operator(token: CompilerToken) -> Option<Option<BinaryOperator>> {
        match token {
            CompilerToken::BitwiseOrAssignment => Some(Some(BinaryOperator::BitwiseOr)),
            CompilerToken::BitwiseAndAssignment => Some(Some(BinaryOperator::BitwiseAnd)),
            CompilerToken::AddAssignment => Some(Some(BinaryOperator::ArithmeticAdd)),
            CompilerToken::SubtractAssignment => Some(Some(BinaryOperator::ArithmeticSubtract)),
            CompilerToken::MultiplyAssignment => Some(Some(BinaryOperator::ArithmeticMultiply)),
            CompilerToken::DivideAssignment => Some(Some(BinaryOperator::ArithmeticDivide)),
            CompilerToken::Assignment => Some(None),
            _ => None,
        }
    }
    fn get_associative_operator_precedence(binary_operator: BinaryOperator) -> u32 {
        match binary_operator {
            BinaryOperator::ArithmeticMultiply => 5,
            BinaryOperator::ArithmeticDivide => 5,
            BinaryOperator::ArithmeticRemainder => 5,
            BinaryOperator::ArithmeticAdd => 6,
            BinaryOperator::ArithmeticSubtract => 6,
            BinaryOperator::BitwiseShiftLeft => 7,
            BinaryOperator::BitwiseShiftRight => 7,
            BinaryOperator::LogicalLess => 9,
            BinaryOperator::LogicalLessEquals => 9,
            BinaryOperator::LogicalMore => 9,
            BinaryOperator::LogicalMoreEquals => 9,
            BinaryOperator::Equals => 10,
            BinaryOperator::NotEquals => 10,
            BinaryOperator::BitwiseAnd => 11,
            BinaryOperator::BitwiseXor => 12,
            BinaryOperator::BitwiseOr => 13,
            BinaryOperator::ShortCircuitAnd => 14,
            BinaryOperator::ShortCircuitOr => 15,
        }
    }
    fn solve_associative_group_step(group: &Vec<AssociativeExpressionGroupOperand>) -> anyhow::Result<usize> {
        let mut lowest_precedence: u32 = u32::MAX;
        let mut lowest_precedence_operator_index: Option<usize> = None;

        for index in 0..group.len() {
            if let AssociativeExpressionGroupOperand::Operator((operator, _)) = group[index] {
                let precedence = Self::get_associative_operator_precedence(operator);
                if lowest_precedence > precedence {
                    lowest_precedence = precedence;
                    lowest_precedence_operator_index = Some(index);
                }
            }
        }
        lowest_precedence_operator_index.ok_or_else(|| anyhow!("Invalid associative group"))
    }
    fn solve_associative_group(group: Vec<AssociativeExpressionGroupOperand>) -> anyhow::Result<Expression> {
        let mut mutable_group: Vec<AssociativeExpressionGroupOperand> = group;

        while mutable_group.len() > 1 {
            let operator_index = Self::solve_associative_group_step(&mutable_group)?;

            let left_expression = if let AssociativeExpressionGroupOperand::Expression(expression) = &mutable_group[operator_index - 1] {
                expression.clone()
            } else { bail!("Invalid associative group") };

            let (operator, source_context) = if let AssociativeExpressionGroupOperand::Operator(operator) = &mutable_group[operator_index] {
                operator.clone()
            } else { bail!("Invalid associative group") };

            let right_expression = if let AssociativeExpressionGroupOperand::Expression(expression) = &mutable_group[operator_index + 1] {
                expression.clone()
            } else { bail!("Invalid associative group") };

            let replacement_expression = BinaryExpression{ left_expression, operator, right_expression, source_context };

            // Replace the group we have just solved with the result of this step
            mutable_group.remove(operator_index + 1);
            mutable_group.remove(operator_index);
            mutable_group[operator_index - 1] = AssociativeExpressionGroupOperand::Expression(Expression::BinaryExpression(Box::new(replacement_expression)))
        }
        if let AssociativeExpressionGroupOperand::Expression(result_expression) = &mutable_group[0] {
            Ok(result_expression.clone())
        } else { bail!("Invalid associative group") }
    }
    fn parse_integer_constant(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let integer_constant_token = self.ctx.next()?;
        let source_context = self.ctx.source_context();
        if let CompilerToken::IntegerLiteral(literal_value) = integer_constant_token {
            let result_expression = IntegerConstantExpression{ constant_value: literal_value, source_context };
            Ok(AmbiguousExpression::unambiguous(self, Expression::IntegerConstantExpression(Box::new(result_expression))))
        } else { Err(self.ctx.fail(format!("Expected integer literal, got {}", integer_constant_token))) }
    }
    fn parse_ambiguous_expression_list<T: Clone, S: Fn(&mut Self) -> anyhow::Result<(T, bool)>>(self, terminator_token: CompilerToken, prefix_parser: S) -> anyhow::Result<AmbiguousParsingResult<'a, Vec<(T, Option<Expression>)>>> {
        self.parse_ambiguous_expression_list_extended(terminator_token, |mut parser| {
            let data = prefix_parser(&mut parser)?;
            Ok(ExactParseCase::create(parser, data))
        }, |parser_case| {
            Ok(parser_case)
        }, |x| x.1.as_ref().unwrap().to_string())
    }
    fn parse_ambiguous_expression_list_extended<T: Clone, R: Clone, PR: Fn(Self) -> anyhow::Result<ExactParseCase<'a, (T, bool)>>, PO: Fn(ExactParseCase<'a, (T, Option<Expression>)>) -> anyhow::Result<ExactParseCase<R>>, POS: Fn(&R) -> String>(mut self, terminator_token: CompilerToken, prefix_parser: PR, postfix_parser: PO, to_string: POS) -> anyhow::Result<AmbiguousParsingResult<'a, Vec<R>>> {
        // Empty expression list is allowed and is not ambiguous
        if self.ctx.peek()? == terminator_token {
            self.ctx.discard_next()?;
            let result_elements: Vec<R> = Vec::new();
            return Ok(AmbiguousParsingResult::unambiguous(self, result_elements))
        }
        let mut finished_cases: Vec<ExactParseCase<'a, Vec<R>>> = Vec::new();
        let mut stashed_arguments: Vec<R> = Vec::new();
        let mut stashed_parser: CompilerParserInstance = self;
        loop {
            // Give the callback a chance to parse the prefix and save some data. If we failed to parse the prefix, use the existing cases
            let prefix_user_data_result = prefix_parser(stashed_parser);
            if prefix_user_data_result.is_err() && !finished_cases.is_empty() {
                break;
            }
            let prefix_user_data_case = prefix_user_data_result?;
            let prefix_parser = prefix_user_data_case.parser;
            let (prefix_user_data, should_digest_expression) = prefix_user_data_case.data;

            // If we should not digest the expression here, just add an element with user data and empty expression to the list
            if !should_digest_expression {
                let postfix_expression_case_result = postfix_parser(ExactParseCase::create(prefix_parser, (prefix_user_data, None)));
                if postfix_expression_case_result.is_err() && !finished_cases.is_empty() {
                    break;
                }
                let mut postfix_expression_case = postfix_expression_case_result?;

                let separator_or_terminator_token = postfix_expression_case.parser.ctx.next()?;
                if separator_or_terminator_token == CompilerToken::Separator {
                    // This is a next item in the argument list, there will be an argument after this one, so just add this argument to the list and continue
                    stashed_arguments.push(postfix_expression_case.data);
                    stashed_parser = postfix_expression_case.parser;
                    continue;
                } else if separator_or_terminator_token == terminator_token {
                    // This is the last argument in the list, construct a new case and add it to the list, and then break
                    let mut complete_arguments: Vec<R> = stashed_arguments.clone();
                    complete_arguments.push(postfix_expression_case.data);
                    finished_cases.push(ExactParseCase::create(postfix_expression_case.parser, complete_arguments));
                    break;
                } else {
                    // This is invalid grammar at this point. If we have other cases parsed, return only them and abandon this stash, otherwise, this is an error (because this would be a first argument missing a terminator after it)
                    if finished_cases.is_empty() {
                        return Err(postfix_expression_case.parser.ctx.fail(format!("Expected , or {}, got {}", terminator_token.clone(), separator_or_terminator_token)));
                    }
                    break;
                }
            }

            // Parse the ambiguous argument and do some processing to remove expressions that cannot be valid under any circumstances (e.g. not followed by item separator or terminator token)
            // If there are no valid combinations, but we have existing cases, assume one of them is valid and this grammar take is not
            let possible_arguments = Self::parse_complete_expression(prefix_parser).and_then(|x| x.flat_map_result(|forked_parser, expression| {
                let mut postfix_expression_case = postfix_parser(ExactParseCase::create(forked_parser, (prefix_user_data.clone(), Some(expression))))?;
                let separator_or_terminator_token = postfix_expression_case.parser.ctx.peek()?;
                if separator_or_terminator_token != terminator_token && separator_or_terminator_token != CompilerToken::Separator {
                    return Err(postfix_expression_case.parser.ctx.fail(format!("Expected , or {}, got {}", terminator_token.clone(), separator_or_terminator_token)))
                };
                Ok(postfix_expression_case.to_parse_result())
            }));
            if possible_arguments.is_err() && !finished_cases.is_empty() {
                break;
            }

            let mut confirmed_argument_values: Vec<ExactParseCase<'a, R>> = Vec::new();
            for mut argument_value in possible_arguments?.cases {
                // Digesting next token is safe here because we have confirmed that this is a valid grammar during earlier disambiguation pass
                let separator_or_terminator_token = argument_value.parser.ctx.next()?;

                // This is a tentative end of the argument list, so add it to the resulting cases
                if separator_or_terminator_token == terminator_token {
                    let mut complete_arguments: Vec<R> = stashed_arguments.clone();
                    complete_arguments.push(argument_value.data);
                    finished_cases.push(ExactParseCase::create(argument_value.parser, complete_arguments))
                } else {
                    // This is not the last argument in the template argument list, as indicated by the comma, which means that we should stash it and continue looking
                    // However, for ambiguous grammar that cannot be resolved at this point, we have to first stash all comma variants and safety check that there is a single one before appending it
                    confirmed_argument_values.push(argument_value);
                }
            }
            // If we have no valid options to continue this argument chain, or this chain is ambiguous, take the existing cases
            if confirmed_argument_values.len() != 1 && !finished_cases.is_empty() {
                break;
            }
            let result_expression_case = AmbiguousParsingResult::from_cases(confirmed_argument_values).disambiguate_generic(|x| to_string(x))?;
            stashed_arguments.push(result_expression_case.data);
            stashed_parser = result_expression_case.parser;
        }
        Ok(AmbiguousParsingResult::from_cases(finished_cases))
    }

    fn parse_ambiguous_template_instantiation_expression<S: Fn(Vec<Expression>) -> Expression>(mut self, mapper: S) -> anyhow::Result<AmbiguousExpression<'a>> {
        let argument_list_enter_token = self.ctx.next()?;
        self.ctx.check_token(argument_list_enter_token, CompilerToken::LessOrArgumentListStart)?;
        Ok(self.parse_ambiguous_expression_list(CompilerToken::MoreOrArgumentListEnd, |_| { Ok(((), true)) })?
            .map_data(|x| mapper(x.into_iter().map(|(_, expr)| expr.unwrap()).collect())))
    }
    fn parse_ambiguous_identifier_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let identifier = self.parse_partial_identifier()?;
        let source_context = self.ctx.source_context();

        if self.ctx.peek_or_eof()? == Some(CompilerToken::LessOrArgumentListStart) {
            // This grammar is ambiguous, because this could be a logical less operator (or less or equals operator) or a template argument list
            // So we have to return both cases if they parse correctly
            self.take_parse_case().repeat(2).flat_map_result(|parser, (_, case_index)| {
                if case_index == 0 {
                    Self::parse_ambiguous_template_instantiation_expression(parser, |arguments| {
                        let result_expression = IdentifierExpression{ identifier: identifier.clone(), source_context: source_context.clone(), template_arguments: Some(arguments) };
                        Expression::IdentifierExpression(Box::new(result_expression))
                    })
                } else {
                    let result_expression = IdentifierExpression{ identifier: identifier.clone(), source_context: source_context.clone(), template_arguments: None };
                    Ok(AmbiguousExpression::unambiguous(parser, Expression::IdentifierExpression(Box::new(result_expression))))
                }
            })
        } else {
            let result_expression = IdentifierExpression{ identifier, source_context, template_arguments: None };
            Ok(AmbiguousExpression::unambiguous(self, Expression::IdentifierExpression(Box::new(result_expression))))
        }
    }
    fn parse_sub_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let sub_expression_entry_token = self.ctx.next()?;
        self.ctx.check_token(sub_expression_entry_token, CompilerToken::SubExpressionStart)?;

        self.parse_complete_expression()?
        .flat_map_result(|mut parser, expression| {
            let sub_expression_exit_token = parser.ctx.next()?;
            parser.ctx.check_token(sub_expression_exit_token, CompilerToken::SubExpressionEnd)?;
            Ok(AmbiguousExpression::unambiguous(parser, expression))
        })
    }
    fn parse_conditional_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let if_expression_token = self.ctx.next()?;
        self.ctx.check_token(if_expression_token, CompilerToken::If)?;
        let source_context = self.ctx.source_context();

        let condition_enter_bracket_token = self.ctx.next()?;
        self.ctx.check_token(condition_enter_bracket_token, CompilerToken::SubExpressionStart)?;

        Ok(Self::parse_complete_expression(self)
        ?.flat_map_result(|mut parser, condition_expr| {
            let condition_exit_bracket_token = parser.ctx.next()?;
            parser.ctx.check_token(condition_exit_bracket_token, CompilerToken::SubExpressionEnd)?;
            Ok(Self::parse_expression_affinity_lowest(parser)?.map_data(|true_expr| (condition_expr.clone(), true_expr)))
        })
        ?.flat_map_result(|mut parser, (condition_expr, true_expr)| {
            let else_expression_token = parser.ctx.next()?;
            parser.ctx.check_token(else_expression_token, CompilerToken::Else)?;
            Ok(Self::parse_expression_affinity_lowest(parser)?.map_data(|false_expr| (condition_expr.clone(), true_expr.clone(), false_expr)))
        })
        ?.map_data(|(condition_expression, true_expression, false_expression)| {
            let result_expression = ConditionalExpression{ condition_expression, true_expression, false_expression, source_context: source_context.clone() };
            Expression::ConditionalExpression(Box::new(result_expression))
        }))
    }
    fn parse_struct_declaration_expression(mut self, struct_kind: UserDefinedTypeKind) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();

        // Next token should be a direct scope entry for struct, inline anonymous struct definitions do not support parent class declarations
        // because they are parsed with the highest affinity, and as such have to be non-ambiguous
        let struct_enter_scope_token = self.ctx.next()?;
        self.ctx.check_token(struct_enter_scope_token, CompilerToken::ScopeStart)?;

        let mut declarations: Vec<StructInnerDeclaration> = Vec::new();

        // Parse struct statements until we encounter the scope exit token
        let mut parser = self;
        while parser.ctx.peek()? != CompilerToken::ScopeEnd {
            let struct_inner_statement = parser.parse_struct_inner_declaration()?;
            declarations.push(struct_inner_statement.data);
            parser = struct_inner_statement.parser;
        }
        // Consume the scope exit token now
        parser.ctx.discard_next()?;
        let result_expression = StructStatement{ declarations, source_context, template_declaration: None, access_specifier: None, struct_kind, alignment_expression: None, name: None, base_class_expressions: Vec::new() };
        Ok(AmbiguousExpression::unambiguous(parser, Expression::StructDeclarationExpression(Box::new(result_expression))))
    }
    fn parse_conditional_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let if_expression_token = self.ctx.next()?;
        self.ctx.check_token(if_expression_token, CompilerToken::If)?;
        let source_context = self.ctx.source_context();

        let condition_enter_bracket_token = self.ctx.next()?;
        self.ctx.check_token(condition_enter_bracket_token, CompilerToken::SubExpressionStart)?;

        self.parse_complete_expression()?.flat_map_result(|mut parser, condition_expression| {
            let condition_exit_bracket_token = parser.ctx.next()?;
            parser.ctx.check_token(condition_exit_bracket_token, CompilerToken::SubExpressionEnd)?;
            Ok(parser.parse_statement()?.map_data(|then_statement| (condition_expression, then_statement)).to_parse_result())
        })?
        .flat_map_result(|mut parser, (condition_expression, then_statement)| {
            if parser.ctx.peek()? == CompilerToken::Else {
                parser.ctx.discard_next()?;
                Ok(parser.parse_statement()?.map_data(|else_statement| (condition_expression, then_statement, Some(else_statement))).to_parse_result())
            } else { Ok(AmbiguousParsingResult::unambiguous(parser, (condition_expression, then_statement, None))) }
        })?
        .map_data(|(condition_expression, then_statement, else_statement)| {
            let result_statement = ConditionalStatement { source_context: source_context.clone(), condition_expression, then_statement, else_statement };
            Statement::ConditionalStatement(Box::new(result_statement))
        }).disambiguate()
    }
    fn parse_block_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let block_enter_token = self.ctx.next()?;
        self.ctx.check_token(block_enter_token, CompilerToken::ScopeStart)?;
        let source_context = self.ctx.source_context();

        let mut statements: Vec<Statement> = Vec::new();
        let mut current_parser = self;
        loop {
            if current_parser.ctx.peek()? == CompilerToken::ScopeEnd {
                current_parser.ctx.discard_next()?;
                let result_statement = BlockStatement{ source_context: source_context.clone(), statements };
                return Ok(ExactStatementCase::create(current_parser, Statement::BlockStatement(Box::new(result_statement))))
            }
            let statement = current_parser.parse_statement()?;
            statements.push(statement.data);
            current_parser = statement.parser;
        }
    }
    fn parse_statement_or_expression(self) -> (anyhow::Result<ExactStatementCase<'a>>, anyhow::Result<AmbiguousExpression<'a>>) {
        (self.clone().parse_statement(), self.parse_complete_expression())
    }
    fn parse_ambiguous_block_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let block_enter_token = self.ctx.next()?;
        self.ctx.check_token(block_enter_token, CompilerToken::ScopeStart)?;
        let source_context = self.ctx.source_context();

        let mut result_cases: Vec<ExactExpressionCase> = Vec::new();
        let mut stashed_statements: Vec<Statement> = Vec::new();
        let mut current_parser = self;
        loop {
            let (statement_result, expression_result) = current_parser.parse_statement_or_expression();
            let terminated_expression = expression_result.and_then(|expr| expr.flat_map_result(|mut parser, possible_expression| {
                let block_exit_token = parser.ctx.next()?;
                parser.ctx.check_token(block_exit_token, CompilerToken::ScopeEnd)?;
                Ok(AmbiguousExpression::unambiguous(parser, possible_expression))
            })).and_then(|expr| expr.disambiguate());
            
            // If we have a valid terminated expression, this is a possible encoding for the expression block, and we should add it to the case list
            if terminated_expression.is_ok() {
                let return_value_expression = terminated_expression?;
                let result_expression = BlockExpression{ statements: stashed_statements.clone(), return_value_expression: return_value_expression.data, source_context: source_context.clone() };
                result_cases.push(ExactExpressionCase::create(return_value_expression.parser, Expression::BlockExpression(Box::new(result_expression))))
            }
            
            // If we could not parse the current stream as a statement, but have already parsed at least one possible block encoding, just return that encoding
            if statement_result.is_err() && !result_cases.is_empty() {
                break;
            }
            
            // Otherwise, push this statement to the statement list and continue looking for the terminating expression
            let statement = statement_result?;
            stashed_statements.push(statement.data);
            current_parser = statement.parser;
        }
        Ok(AmbiguousExpression::from_cases(result_cases))
    }
    fn parse_assignment_statement(self) -> anyhow::Result<ExactStatementCase<'a>> {
        let source_context = self.ctx.source_context();
        self.parse_complete_expression()?.flat_map_result(|mut parser, left_hand_expression| {
            let operator_token = parser.ctx.next()?;
            let assignment_operator = Self::try_parse_assignment_operator(operator_token.clone())
                .ok_or_else(|| parser.ctx.fail(format!("Expected |=,&=, +=, -=, *=, /= or =, got {}", operator_token)))?;
            Ok(parser.parse_complete_expression()?.map_data(|assignment_expression| (left_hand_expression.clone(), assignment_operator, assignment_expression)))
        })?
        .flat_map_result(|mut parser, (left_hand_expression, assignment_operator, assignment_expression)| {
            let terminator_token = parser.ctx.next()?;
            parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

            let result_statement = AssignmentStatement{ source_context: source_context.clone(), left_hand_expression, assignment_operator, assignment_expression };
            Ok(AmbiguousParsingResult::unambiguous(parser, Statement::AssignmentStatement(Box::new(result_statement))))
        })?.disambiguate()
    }
    fn parse_local_var_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        self.ctx.discard_next()?;

        let value_type_token = self.ctx.next()?;
        let value_type = self.parse_expression_value_type(value_type_token)?;

        let source_context = self.ctx.source_context();
        let variable_name_token = self.ctx.next()?;
        let name = self.ctx.check_identifier(variable_name_token)?;

        if self.ctx.peek()? == CompilerToken::Assignment {
            self.ctx.discard_next()?;

            self.parse_complete_expression()?.flat_map_result(|mut parser, initializer_expression| {
                let terminator_token = parser.ctx.next()?;
                parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

                let result_statement = DeclarationStatement { source_context: source_context.clone(), value_type, name: name.clone(), initializer: Some(initializer_expression) };
                Ok(AmbiguousParsingResult::unambiguous(parser, Statement::DeclarationStatement(Box::new(result_statement))))
            })?.disambiguate()
        } else {
            let terminator_token = self.ctx.next()?;
            self.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

            let result_statement = DeclarationStatement { source_context: source_context.clone(), value_type, name, initializer: None };
            Ok(ExactStatementCase::create(self, Statement::DeclarationStatement(Box::new(result_statement))))
        }
    }
    fn parse_while_loop_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let while_loop_token = self.ctx.next()?;
        self.ctx.check_token(while_loop_token, CompilerToken::While)?;
        let source_context = self.ctx.source_context();

        let condition_enter_bracket_token = self.ctx.next()?;
        self.ctx.check_token(condition_enter_bracket_token, CompilerToken::SubExpressionStart)?;

        self.parse_complete_expression()?
        .flat_map_result(|mut parser, condition_expression| {
            let condition_exit_bracket_token = parser.ctx.next()?;
            parser.ctx.check_token(condition_exit_bracket_token, CompilerToken::SubExpressionEnd)?;
            Ok(parser.parse_statement()?.map_data(|loop_body_statement| (condition_expression, loop_body_statement)).to_parse_result())
        })?
        .map_data(|(condition_expression, loop_body_statement)| {
            let result_statement = WhileLoopStatement{ source_context: source_context.clone(), condition_expression, loop_body_statement };
            Statement::WhileLoopStatement(Box::new(result_statement))
        }).disambiguate()
    }
    fn parse_break_loop_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let break_loop_token = self.ctx.next()?;
        self.ctx.check_token(break_loop_token, CompilerToken::Break)?;
        let source_context = self.ctx.source_context();

        let terminator_token = self.ctx.next()?;
        self.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

        let result_statement = SimpleStatement{source_context};
        Ok(ExactStatementCase::create(self, Statement::BreakLoopStatement(Box::new(result_statement))))
    }
    fn parse_continue_loop_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let break_loop_token = self.ctx.next()?;
        self.ctx.check_token(break_loop_token, CompilerToken::Continue)?;
        let source_context = self.ctx.source_context();

        let terminator_token = self.ctx.next()?;
        self.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

        let result_statement = SimpleStatement{source_context};
        Ok(ExactStatementCase::create(self, Statement::ContinueLoopStatement(Box::new(result_statement))))
    }
    fn parse_empty_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let source_context = self.ctx.source_context();
        let terminator_token = self.ctx.next()?;
        self.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

        let result_statement = SimpleStatement{source_context};
        Ok(ExactParseCase::create(self, Statement::EmptyStatement(Box::new(result_statement))))
    }
    fn parse_statement(mut self) -> anyhow::Result<ExactStatementCase<'a>> {
        let first_statement_token = self.ctx.peek()?;
        match first_statement_token {
            CompilerToken::If => self.parse_conditional_statement(),
            CompilerToken::While => self.parse_while_loop_statement(),
            CompilerToken::Break => self.parse_break_loop_statement(),
            CompilerToken::Continue => self.parse_continue_loop_statement(),
            CompilerToken::Terminator => self.parse_empty_statement(),
            CompilerToken::ScopeStart => self.parse_block_statement(),
            CompilerToken::Let => self.parse_local_var_statement(),
            _ => self.parse_assignment_statement(), // assume anything else is an assignment statement (because it starts with an expression)
        }
    }
    fn parse_unary_expression(mut self, operator: UnaryOperator) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        self.parse_expression_affinity_medium()?
        .flat_map_result(|parser, expression| {
            let result_expression = UnaryExpression{ operator, expression, source_context: source_context.clone() };
            Ok(AmbiguousExpression::unambiguous(parser, Expression::UnaryExpression(Box::new(result_expression))))
        })
    }
    fn parse_array_type_expression(mut self, element_type_expression: Expression) -> anyhow::Result<AmbiguousExpression<'a>> {
        let array_enter_expression = self.ctx.next()?;
        self.ctx.check_token(array_enter_expression, CompilerToken::ArraySubscriptStart)?;
        let source_context = self.ctx.source_context();

        self.parse_complete_expression()?
        .flat_map_result(|mut parser, length_expression| {
            let array_exit_expression = parser.ctx.next()?;
            parser.ctx.check_token(array_exit_expression, CompilerToken::ArraySubscriptEnd)?;
            let result_expression = ArrayTypeExpression { element_type_expression: element_type_expression.clone(), array_length_expression: length_expression, source_context: source_context.clone() };
            Self::wrap_expression_with_possible_cv_qualifiers(AmbiguousExpression::unambiguous(parser, Expression::ArrayIndexExpression(Box::new(result_expression))))
        })
    }
    fn parse_bracketed_unary_operator_expression(mut self, operator: UnaryOperator) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let enter_bracket_token = self.ctx.next()?;
        let source_context = self.ctx.source_context();
        self.ctx.check_token(enter_bracket_token, CompilerToken::SubExpressionStart)?;

        // Bracketed operators are pre-delimited and as such have the highest priority
        self.parse_complete_expression()?
            .flat_map_result(|mut parser, expression| {
                let exit_bracket_token = parser.ctx.next()?;
                parser.ctx.check_token(exit_bracket_token, CompilerToken::SubExpressionEnd)?;

                let result_expression = UnaryExpression { operator, expression, source_context: source_context.clone() };
                Ok(AmbiguousExpression::unambiguous(parser, Expression::UnaryExpression(Box::new(result_expression))))
            })
    }
    fn parse_builtin_expression(mut self, identifier: BuiltinIdentifier) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        let result_expression = BuiltinIdentifierExpression{identifier, source_context};
        Ok(AmbiguousExpression::unambiguous(self, Expression::BuiltinIdentifierExpression(Box::new(result_expression))))
    }
    fn parse_simple_primitive_type_expression(mut self, primitive_type: PrimitiveType) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        let result_expression = PrimitiveTypeExpression{primitive_type, source_context};
        Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
    }
    fn parse_unsigned_long_primitive_type_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let source_context = self.ctx.source_context();
        self.ctx.discard_next()?;

        let first_expression_token = self.ctx.peek_or_eof()?;
        if first_expression_token == Some(CompilerToken::PrimitiveModifierLong) {
            self.ctx.discard_next()?;
            // Can only mean unsigned long long [int] at this point, but if int is given explicitly, digest it
            if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
                self.ctx.discard_next()?;
            }
            let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::UnsignedLongLongInt, source_context};
            Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
        } else {
            // Can only mean unsigned long [int] at this point, but if int is given explicitly, digest it
            if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
                self.ctx.discard_next()?;
            }
            let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::UnsignedLongInt, source_context};
            Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
        }
    }
    fn parse_unsigned_short_primitive_type_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let source_context = self.ctx.source_context();
        self.ctx.discard_next()?;
        // Result is always the same, unsigned short can only mean unsigned short [int], but if int is given explicitly consume it too
        if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
            self.ctx.discard_next()?;
        }
        let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::UnsignedShortInt, source_context};
        Ok(AmbiguousExpression::unambiguous( self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
    }
    fn parse_unsigned_primitive_type_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        let first_expression_token = self.ctx.peek_or_eof()?;
        match first_expression_token {
            Some(CompilerToken::PrimitiveTypeChar) => self.parse_simple_primitive_type_expression(PrimitiveType::UnsignedChar),
            Some(CompilerToken::PrimitiveTypeInt) => self.parse_simple_primitive_type_expression(PrimitiveType::UnsignedInt),
            Some(CompilerToken::PrimitiveModifierLong) => self.parse_unsigned_long_primitive_type_expression(),
            Some(CompilerToken::PrimitiveModifierShort) => self.parse_unsigned_short_primitive_type_expression(),
            _ => {
                // everything else is treated as unsigned [int]
                let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::UnsignedInt, source_context};
                Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
            },
        }
    }
    fn parse_short_primitive_type_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        // Result is always the same, short can only mean short [int], but if int is given explicitly consume it too
        if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
            self.ctx.discard_next()?;
        }
        let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::ShortInt, source_context};
        Ok(AmbiguousExpression::unambiguous( self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
    }
    fn parse_long_primitive_type_expression(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let source_context = self.ctx.source_context();
        self.ctx.discard_next()?;

        let first_expression_token = self.ctx.peek_or_eof()?;
        if first_expression_token == Some(CompilerToken::PrimitiveModifierLong) {
            self.ctx.discard_next()?;
            // Can only mean long long [int] at this point, but if int is given explicitly, digest it
            if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
                self.ctx.discard_next()?;
            }
            let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::LongLongInt, source_context};
            Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
        } else {
            // Can only mean long [int] at this point, but if int is given explicitly, digest it
            if self.ctx.peek_or_eof()? == Some(CompilerToken::PrimitiveTypeInt) {
                self.ctx.discard_next()?;
            }
            let result_expression = PrimitiveTypeExpression{primitive_type: PrimitiveType::LongInt, source_context};
            Ok(AmbiguousExpression::unambiguous(self, Expression::PrimitiveTypeExpression(Box::new(result_expression))))
        }
    }
    fn parse_expression_affinity_highest(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let first_expression_token = self.ctx.peek()?;
        match first_expression_token {
            CompilerToken::IntegerLiteral(_) => self.parse_integer_constant(),
            CompilerToken::Identifier(_) => self.parse_ambiguous_identifier_expression(),
            CompilerToken::Sizeof => self.parse_bracketed_unary_operator_expression(UnaryOperator::StructSizeOf),
            CompilerToken::Alignof => self.parse_bracketed_unary_operator_expression(UnaryOperator::StructAlignOf),
            CompilerToken::SubExpressionStart => self.parse_sub_expression(),
            CompilerToken::ScopeStart => Ok(self.parse_ambiguous_block_expression()?),
            CompilerToken::Struct => self.parse_struct_declaration_expression(UserDefinedTypeKind::Struct),
            CompilerToken::Class => self.parse_struct_declaration_expression(UserDefinedTypeKind::Class),
            CompilerToken::Union => self.parse_struct_declaration_expression(UserDefinedTypeKind::Union),
            CompilerToken::BuiltinAddressSize => self.parse_builtin_expression(BuiltinIdentifier::AddressSize),
            CompilerToken::BuiltinTargetPlatform => self.parse_builtin_expression(BuiltinIdentifier::TargetPlatform),
            CompilerToken::BuiltinTargetArch => self.parse_builtin_expression(BuiltinIdentifier::TargetArch),
            CompilerToken::PrimitiveTypeVoid => self.parse_simple_primitive_type_expression(PrimitiveType::Void),
            CompilerToken::PrimitiveTypeChar => self.parse_simple_primitive_type_expression(PrimitiveType::Char),
            CompilerToken::PrimitiveTypeWideChar => self.parse_simple_primitive_type_expression(PrimitiveType::WideChar),
            CompilerToken::PrimitiveTypeInt => self.parse_simple_primitive_type_expression(PrimitiveType::Int),
            CompilerToken::PrimitiveTypeBool => self.parse_simple_primitive_type_expression(PrimitiveType::Bool),
            CompilerToken::PrimitiveTypeFloat => self.parse_simple_primitive_type_expression(PrimitiveType::Float),
            CompilerToken::PrimitiveTypeDouble => self.parse_simple_primitive_type_expression(PrimitiveType::Double),
            CompilerToken::PrimitiveTypeChar8 => self.parse_simple_primitive_type_expression(PrimitiveType::Char8),
            CompilerToken::PrimitiveTypeChar16 => self.parse_simple_primitive_type_expression(PrimitiveType::Char16),
            CompilerToken::PrimitiveTypeChar32 => self.parse_simple_primitive_type_expression(PrimitiveType::Char32),
            CompilerToken::PrimitiveModifierUnsigned => self.parse_unsigned_primitive_type_expression(),
            CompilerToken::PrimitiveModifierShort => self.parse_short_primitive_type_expression(),
            CompilerToken::PrimitiveModifierLong => self.parse_long_primitive_type_expression(),
            _ => Err(self.ctx.fail(format!("Expected expression, got {}", first_expression_token))),
        }
    }
    fn parse_single_member_access_expression(mut self, nested_expression: Expression) -> anyhow::Result<AmbiguousExpression<'a>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();

        let member_type_token = self.ctx.next()?;
        let member_type = self.parse_expression_value_type(member_type_token)?;

        let member_name_token = self.ctx.next()?;
        let member_name = self.ctx.check_identifier(member_name_token)?;

        if self.ctx.peek()? == CompilerToken::LessOrArgumentListStart {
            // This grammar is ambiguous, because this could be a logical less operator (or less or equals operator) or a template argument list
            // So we have to return both cases if they parse correctly
            self.take_parse_case().repeat(2).flat_map_result(|parser, (_, case_index)| {
                if case_index == 0 {
                    Self::parse_ambiguous_template_instantiation_expression(parser, |arguments| {
                        let result_expression = MemberAccessExpression{ type_expression: nested_expression.clone(), member_type, member_name: member_name.clone(), source_context: source_context.clone(), template_arguments: Some(arguments) };
                        Expression::MemberAccessExpression(Box::new(result_expression))
                    })
                } else {
                    let result_expression = MemberAccessExpression{ type_expression: nested_expression.clone(), member_type, member_name: member_name.clone(), source_context: source_context.clone(), template_arguments: None };
                    Ok(AmbiguousExpression::unambiguous(parser, Expression::MemberAccessExpression(Box::new(result_expression))))
                }
            })
        } else {
            let result_expression = MemberAccessExpression{ type_expression: nested_expression, member_type, member_name, source_context, template_arguments: None };
            Ok(AmbiguousExpression::unambiguous(self, Expression::MemberAccessExpression(Box::new(result_expression))))
        }
    }
    fn parse_expression_affinity_higher(self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let mut unexplored_cases: Vec<ExactExpressionCase<'a>> = Vec::new();
        let mut result_cases: Vec<ExactExpressionCase<'a>> = Vec::new();
        let mut failed_cases: Vec<anyhow::Error> = Vec::new();

        unexplored_cases.append(&mut self.parse_expression_affinity_highest()?.cases);
        while !unexplored_cases.is_empty() {
            let mut current_case = unexplored_cases.pop().unwrap();

            // If this case is a member access expression, parse it
            if let Ok(result) = current_case.parser.ctx.peek_or_eof() && result == Some(CompilerToken::ScopeDelimiter) {
                match current_case.parser.parse_single_member_access_expression(current_case.data) {
                    Ok(mut parsed_expression) => {
                        // If we successfully parsed member access expression, add it to the unexplored list, since it could be a chain
                        unexplored_cases.append(&mut parsed_expression.cases);
                    }
                    Err(expression_parse_error) => {
                        failed_cases.push(expression_parse_error);
                    }
                }
            } else {
                // This case does not have member access expressions left on the tail, so add it to the results directly
                result_cases.push(current_case)
            }
        }
        AmbiguousExpression::checked_from_cases(result_cases, failed_cases)
    }
    fn wrap_expression_with_possible_cv_qualifiers(ambiguous_expression: AmbiguousExpression<'a>) -> anyhow::Result<AmbiguousExpression<'a>> {
        ambiguous_expression.flat_map_result(|mut parser, expression| {
            let source_context = parser.ctx.source_context();
            let mut seen_const = false;
            let mut seen_volatile = false;
            loop {
                let next_token = parser.ctx.peek_or_eof()?;
                if next_token == Some(CompilerToken::Const) {
                    if seen_const { return Err(parser.ctx.fail("Duplicate const modifier applied to type")); }
                    parser.ctx.discard_next()?;
                    seen_const = true;
                } else if next_token == Some(CompilerToken::Volatile) {
                    if seen_volatile { return Err(parser.ctx.fail("Duplicate volatile modifier applied to type")); }
                    parser.ctx.discard_next()?;
                    seen_volatile = true;
                } else { break; }
            }
            if seen_const || seen_volatile {
                let result_expression = CVQualifiedExpression{base_expression: expression, constant: seen_const, volatile: seen_volatile, source_context};
                Ok(AmbiguousParsingResult::unambiguous(parser, Expression::CVQualifiedExpression(Box::new(result_expression))))
            } else {
                Ok(AmbiguousParsingResult::unambiguous(parser, expression))
            }
        })
    }
    fn parse_expression_affinity_high(self) -> anyhow::Result<AmbiguousExpression<'a>> {
        Self::wrap_expression_with_possible_cv_qualifiers(self.parse_expression_affinity_higher()?)?
        .flat_map_result(|mut parser, simple_expression| {
            if parser.ctx.peek_or_eof()? == Some(CompilerToken::PointerOrMultiply) {
                // This could be a pointer unary operator, but this is ambiguous because it could also be interpreted as a start of multiplication binary operator
                // So we need to pursue both options, and hopefully we will be able to disambiguate them later
                ExactExpressionCase{ parser, data: simple_expression }.repeat(2).flat_map_result(|mut forked_parser, (expression, case_index)| {
                    if case_index == 0 {
                        // This is a pointer unary operator case, so consume the pointer token now
                        let pointer_operator_token = forked_parser.ctx.next()?;
                        forked_parser.ctx.check_token(pointer_operator_token, CompilerToken::PointerOrMultiply)?;
                        let source_context = forked_parser.ctx.source_context();

                        let result_expression = UnaryExpression{ operator: UnaryOperator::StructMakePointer, expression, source_context };
                        Self::wrap_expression_with_possible_cv_qualifiers(AmbiguousExpression::unambiguous(forked_parser, Expression::UnaryExpression(Box::new(result_expression))))
                    } else {
                        // This is a normal case where we do not digest the pointer token, so just return the expression as-is
                        Ok(AmbiguousExpression::unambiguous(forked_parser, expression))
                    }
                })
            } else if parser.ctx.peek_or_eof()? == Some(CompilerToken::ArraySubscriptStart) {
                // Array index expression is unambiguous, so we do not need to fork the context on it
                Self::parse_array_type_expression(parser, simple_expression)
            } else {
                // This is a high affinity expression without any postscript operators
                Ok(AmbiguousExpression::unambiguous(parser, simple_expression))
            }
        })
    }
    fn parse_expression_affinity_medium(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let first_expression_token = self.ctx.peek()?;
        match first_expression_token {
            CompilerToken::BitwiseInverse => self.parse_unary_expression(UnaryOperator::BitwiseInverse),
            CompilerToken::NegateOrSubtract => self.parse_unary_expression(UnaryOperator::ArithmeticNegate),
            CompilerToken::BoolNegate => self.parse_unary_expression(UnaryOperator::BoolNegate),
            _ => self.parse_expression_affinity_high(),
        }
    }
    fn parse_expression_affinity_low(self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let mut result_cases: Vec<ExactExpressionCase> = Vec::new();
        let mut stashed_elements: Vec<AssociativeExpressionGroupOperand> = Vec::new();
        let mut current_parser: CompilerParserInstance = self;
        loop {
            // If we cannot parse the current element expression successfully, but we have some tentative forms that we parsed in the past,
            // just assume that the current form is not valid and the previous ones are the ones that are ambiguous
            let ambiguous_element_expression = current_parser.parse_expression_affinity_medium();
            if ambiguous_element_expression.is_err() && !result_cases.is_empty() {
                break;
            }
            let mut element_expression_variants: Vec<(ExactExpressionCase, (BinaryOperator, ASTSourceContext))> = Vec::new();

            for mut element_expression in ambiguous_element_expression?.cases {
                let mut operator = element_expression.parser.ctx.peek_or_eof()?
                    .and_then(|x| Self::try_parse_binary_operator(x))
                    .map(|(x, y)| ((x, element_expression.parser.ctx.source_context()), y));

                // If there is not a binary operator following this expression, we have successfully completed an associative group, so break from the loop and add it to the list
                // If there is an operator that can be ambiguous, we also want to copy the associative group and terminate it here, but still attempt to complete it
                if operator.is_none() || operator.as_ref().unwrap().1 {
                    let mut result_elements = stashed_elements.clone();
                    result_elements.push(AssociativeExpressionGroupOperand::Expression(element_expression.data.clone()));

                    let result_expression = Self::solve_associative_group(result_elements)?;
                    result_cases.push(ExactExpressionCase { data: result_expression, parser: element_expression.parser.clone() });
                    if operator.is_none() {
                        continue;
                    }
                }
                // Binary operator is following this expression, which means that it might be another element of the associative group
                element_expression.parser.ctx.discard_next()?;

                // Special case to support >>, it has to digested as two separate tokens to avoid incorrect lexing of two nested templates as a single token (like A<B<C>>)
                let secondary_operator = element_expression.parser.ctx.peek_or_eof()?.and_then(|x| Self::try_parse_binary_operator(x));
                if operator.as_ref().map(|x| x.0.0 == BinaryOperator::LogicalMore).unwrap_or(false) && secondary_operator == Some((BinaryOperator::LogicalMore, true)) {
                    element_expression.parser.ctx.discard_next()?;
                    operator = Some(((BinaryOperator::BitwiseShiftRight, operator.unwrap().0.1), true));
                }
                element_expression_variants.push((element_expression, operator.unwrap().0));
            }

            // If we have no variants or an ambiguous variant for this element, then we need to take one of the existing cases, and this chain is over
            if element_expression_variants.len() != 1 {
                break;
            }

            let (new_element_expression, next_operator) = element_expression_variants.pop().unwrap();
            stashed_elements.push(AssociativeExpressionGroupOperand::Expression(new_element_expression.data));
            stashed_elements.push(AssociativeExpressionGroupOperand::Operator(next_operator));
            current_parser = new_element_expression.parser;
        }
        Ok(AmbiguousExpression::from_cases(result_cases))
    }
    fn parse_expression_affinity_lowest(mut self) -> anyhow::Result<AmbiguousExpression<'a>> {
        let first_expression_token = self.ctx.peek()?;
        match first_expression_token {
            CompilerToken::If => self.parse_conditional_expression(),
            _ => self.parse_expression_affinity_low(),
        }
    }
    fn parse_complete_expression(self) -> anyhow::Result<AmbiguousExpression<'a>> {
        // Associative expression group is the highest level expression
        self.parse_expression_affinity_lowest()
    }

    fn parse_template_declaration(mut self) -> anyhow::Result<AmbiguousParsingResult<'a, TemplateDeclaration>> {
        let template_token = self.ctx.next()?;
        self.ctx.check_token(template_token, CompilerToken::Template)?;

        let template_argument_start_token = self.ctx.next()?;
        self.ctx.check_token(template_argument_start_token, CompilerToken::LessOrArgumentListStart)?;

        Ok(self.parse_ambiguous_expression_list(CompilerToken::MoreOrArgumentListEnd, |parser| {
            let argument_type_token = parser.ctx.next()?;
            let value_type = parser.parse_expression_value_type(argument_type_token)?;
            let source_context = parser.ctx.source_context();

            let argument_name_token = parser.ctx.next()?;
            let name = parser.ctx.check_identifier(argument_name_token)?;

            let mut should_parse_default_value_expression = false;
            if parser.ctx.peek()? == CompilerToken::Assignment {
                parser.ctx.discard_next()?;
                should_parse_default_value_expression = true;
            }
            Ok(((value_type, name, source_context), should_parse_default_value_expression))
        })?.map_data(|raw_arguments| {
            let arguments: Vec<TemplateArgument> = raw_arguments.into_iter().map(|((value_type, name, source_context), default_value)| {
                TemplateArgument{ name, value_type, default_value, source_context }
            }).collect();
            TemplateDeclaration{arguments}
        }))
    }
    fn parse_import_statement(mut self) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        let import_statement_token = self.ctx.next()?;
        self.ctx.check_token(import_statement_token, CompilerToken::Import)?;
        let source_context = self.ctx.source_context();

        let namespace_or_qualified_import = self.parse_partial_identifier()?;
        let complex_import_start_or_terminator = self.ctx.next()?;

        // This is a complex import, potentially with aliases for imported types
        if complex_import_start_or_terminator == CompilerToken::ScopeDelimiter {
            let scope_start_token = self.ctx.next()?;
            self.ctx.check_token(scope_start_token, CompilerToken::ScopeStart)?;

            let mut composite_import = ModuleCompositeImport{namespace: namespace_or_qualified_import, imported_names: Vec::new()};

            // Composite import should include at least one item to be valid
            loop {
                let original_name_token = self.ctx.next()?;
                let original_name = self.ctx.check_identifier(original_name_token)?;
                composite_import.imported_names.push(original_name);

                // If next token is the scope exit, we have completely processed the import
                let next_token = self.ctx.next()?;
                if next_token == CompilerToken::ScopeEnd {
                    break;
                }
                // Otherwise we should have a comma separating this from the next import item
                self.ctx.check_token(next_token, CompilerToken::Separator)?
            }

            // Should be finished with a statement terminator
            let next_token = self.ctx.next()?;
            self.ctx.check_token(next_token, CompilerToken::Terminator)?;

            let result_statement = ModuleImportStatement{statement_type: ModuleImportStatementType::CompositeImport(composite_import), source_context};
            return Ok(ExactModuleTopLevelDeclarationCase::create(self, ModuleTopLevelDeclaration::ImportStatement(result_statement)));
        }

        // Normal qualified import ending with a statement terminator
        self.ctx.check_token(complex_import_start_or_terminator, CompilerToken::Terminator)?;
        let result_statement = ModuleImportStatement{statement_type: ModuleImportStatementType::QualifiedImport(namespace_or_qualified_import), source_context};
        Ok(ExactModuleTopLevelDeclarationCase::create(self, ModuleTopLevelDeclaration::ImportStatement(result_statement)))
    }
    fn parse_input_statement(mut self, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        let statement_token = self.ctx.next()?;
        self.ctx.check_token(statement_token, CompilerToken::Input)?;
        let source_context = self.ctx.source_context();

        let value_type_token = self.ctx.next()?;
        let value_type = self.parse_expression_value_type(value_type_token)?;
        let global_name_token = self.ctx.next()?;
        let global_name = self.ctx.check_identifier(global_name_token)?;

        if self.ctx.peek_or_eof()? == Some(CompilerToken::Assignment) {
            self.ctx.discard_next()?;
            Ok(self.parse_complete_expression()?.flat_map_result(|mut parser, expression| {
                // Should end with a statement terminator
                let terminator_token = parser.ctx.next()?;
                parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

                // Input variable declaration with default value
                let result_statement = InputStatement{source_context: source_context.clone(), global_name: global_name.clone(), access_specifier, value_type, default_value: Some(expression)};
                Ok(AmbiguousParsingResult::unambiguous(parser, ModuleTopLevelDeclaration::InputStatement(result_statement)))
            })?.disambiguate()?)
        } else {
            // Should end with a statement terminator
            let terminator_token = self.ctx.next()?;
            self.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

            // Input variable declaration with no default value
            let result_statement = InputStatement{source_context, global_name, access_specifier, value_type, default_value: None};
            Ok(ExactModuleTopLevelDeclarationCase::create(self, ModuleTopLevelDeclaration::InputStatement(result_statement)))
        }
    }
    fn parse_constexpr_statement(mut self, template_declaration: Option<TemplateDeclaration>, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactParseCase<'a, DataStatement>> {
        self.ctx.discard_next()?;

        let value_type_token = self.ctx.next()?;
        let value_type = self.parse_expression_value_type(value_type_token)?;
        if value_type == ExpressionValueType::Typename {
            return Err(self.ctx.fail("Typename not allowed as constexpr declaration type. Use type alias instead"));
        }
        self.parse_data_statement_internal(value_type, template_declaration, access_specifier)
    }
    fn parse_type_statement(mut self, template_declaration: Option<TemplateDeclaration>, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactParseCase<'a, DataStatement>> {
        self.ctx.discard_next()?;
        self.parse_data_statement_internal(ExpressionValueType::Typename, template_declaration, access_specifier)
    }
    fn parse_data_statement_internal(mut self, value_type: ExpressionValueType, template_declaration: Option<TemplateDeclaration>, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactParseCase<'a, DataStatement>> {
        let source_context = self.ctx.source_context();
        let data_name_token = self.ctx.next()?;
        let name = self.ctx.check_identifier(data_name_token)?;

        // All data statements must be immediately assigned to a value, since they are actually functions and not real data with persistent storage
        let assignment_operator_token = self.ctx.next()?;
        self.ctx.check_token(assignment_operator_token, CompilerToken::Assignment)?;

        let initializer = self.parse_complete_expression()?.flat_map_result(|mut parser, expression| {
            // Should end with a statement terminator to be considered valid
            let terminator_token = parser.ctx.next()?;
            parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;
            Ok(AmbiguousExpression::unambiguous(parser, expression))
        })?.disambiguate()?;
        Ok(initializer.map_data(|x| DataStatement { source_context: source_context.clone(), template_declaration, access_specifier, value_type, name, initializer: x }))
    }
    fn parse_struct_conditional_declaration(mut self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        let conditional_statement_token = self.ctx.next()?;
        self.ctx.check_token(conditional_statement_token, CompilerToken::If)?;
        let source_context = self.ctx.source_context();
        let condition_enter_bracket_token = self.ctx.next()?;
        self.ctx.check_token(condition_enter_bracket_token, CompilerToken::SubExpressionStart)?;

        Ok(self.parse_complete_expression()?
            .flat_map_result(|mut parser, expression| {
                let condition_exit_bracket_token = parser.ctx.next()?;
                parser.ctx.check_token(condition_exit_bracket_token, CompilerToken::SubExpressionEnd)?;
                Ok(AmbiguousExpression::unambiguous(parser, expression))
            })?.disambiguate()?
            .map_result(|parser, condition_expression| {
                Ok(parser.parse_struct_inner_declaration()?.map_data(|then_branch| (condition_expression, then_branch)))
            })?
            .map_result(|mut parser, (condition_expression, then_branch)| {
                if parser.ctx.peek()? == CompilerToken::Else {
                    parser.ctx.discard_next()?;
                    Ok(parser.parse_struct_inner_declaration()?.map_data(|else_branch| (condition_expression, then_branch, Some(else_branch))))
                } else { Ok(ExactParseCase::create(parser, (condition_expression, then_branch, None))) }
            })?
            .map_data(|(condition_expression, then_branch, else_branch)| {
                let conditional_statement = ConditionalDeclaration { source_context: source_context.clone(), condition_expression, then_branch, else_branch };
                StructInnerDeclaration::ConditionalDeclaration(Box::new(conditional_statement))
            }))
    }
    fn parse_optional_alignment_expression(mut self) -> anyhow::Result<ExactParseCase<'a, Option<Expression>>> {
        // Parse optional alignment expression
        if self.ctx.peek()? == CompilerToken::Alignas {
            self.ctx.discard_next()?;
            let alignment_expression_open_bracket = self.ctx.next()?;
            self.ctx.check_token(alignment_expression_open_bracket, CompilerToken::SubExpressionStart)?;

            Ok(self.parse_complete_expression()?
                .flat_map_result(|mut parser, expression| {
                    let alignment_expression_close_bracket = parser.ctx.next()?;
                    parser.ctx.check_token(alignment_expression_close_bracket, CompilerToken::SubExpressionEnd)?;
                    Ok(AmbiguousExpression::unambiguous(parser, expression))
                })?.disambiguate()?.map_data(|x| Some(x)))
        } else {
            Ok(ExactParseCase::create(self, None))
        }
    }
    fn parse_struct_member_declaration(self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        let source_context = self.ctx.source_context();
        self.parse_optional_alignment_expression()?
            .map_result(|parser, alignment_expression| {
                Ok(parser.parse_complete_expression()?.map_data(|x| (alignment_expression.clone(), x)))
            })?
            .flat_map_result(|mut parser, (alignment_expression, member_type_expression)| {
                let name_token = parser.ctx.next()?;
                let name = parser.ctx.check_identifier(name_token)?;
                let parsed_next_token = parser.ctx.next()?;

                if parsed_next_token == CompilerToken::ArraySubscriptStart {
                    // This is an array field, parse the array size expression
                    Ok(parser.parse_complete_expression()?
                        .flat_map_result(|mut inner_parser, expression| {
                            let array_terminator_token = inner_parser.ctx.next()?;
                            inner_parser.ctx.check_token(array_terminator_token, CompilerToken::ArraySubscriptEnd)?;

                            let statement_terminator_token = inner_parser.ctx.next()?;
                            inner_parser.ctx.check_token(statement_terminator_token, CompilerToken::Terminator)?;

                            Ok(AmbiguousExpression::unambiguous(inner_parser, expression))
                        })?.disambiguate()?
                        .map_data(|array_size_expression| {
                            let result_declaration = MemberDeclaration { source_context: source_context.clone(), alignment_expression: alignment_expression.clone(), member_type_expression, name, array_size_expression: Some(array_size_expression), bitfield_width_expression: None };
                            StructInnerDeclaration::MemberDeclaration(Box::new(result_declaration))
                        }).to_parse_result())
                } else if parsed_next_token == CompilerToken::BaseClass {
                    // This is a bitfield, parse the bitfield width expression
                    Ok(parser.parse_complete_expression()?
                        .flat_map_result(|mut inner_parser, expression| {
                            let statement_terminator_token = inner_parser.ctx.next()?;
                            inner_parser.ctx.check_token(statement_terminator_token, CompilerToken::Terminator)?;

                            Ok(AmbiguousExpression::unambiguous(inner_parser, expression))
                        })?.disambiguate()?
                        .map_data(|bitfield_width_expression| {
                            let result_declaration = MemberDeclaration { source_context: source_context.clone(), alignment_expression: alignment_expression.clone(), member_type_expression, name, array_size_expression: None, bitfield_width_expression: Some(bitfield_width_expression) };
                            StructInnerDeclaration::MemberDeclaration(Box::new(result_declaration))
                        }).to_parse_result())
                } else {
                    // This is a normal member, not a bitfield or an array
                    parser.ctx.check_token(parsed_next_token, CompilerToken::Terminator)?;
                    let result_declaration = MemberDeclaration { source_context: source_context.clone(), alignment_expression: alignment_expression.clone(), member_type_expression, name, array_size_expression: None, bitfield_width_expression: None };
                    Ok(ExactStructInnerDeclarationCase::create(parser, StructInnerDeclaration::MemberDeclaration(Box::new(result_declaration))).to_parse_result())
                }
            })?.disambiguate()
    }
    fn parse_struct_block_declaration(mut self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        let scope_enter_token = self.ctx.next()?;
        self.ctx.check_token(scope_enter_token, CompilerToken::ScopeStart)?;
        let source_context = self.ctx.source_context();
        let mut declarations: Vec<StructInnerDeclaration> = Vec::new();

        let mut current_parser = self;
        while current_parser.ctx.peek()? != CompilerToken::ScopeEnd {
            let declaration = current_parser.parse_struct_inner_declaration()?;
            declarations.push(declaration.data);
            current_parser = declaration.parser;
        }
        current_parser.ctx.discard_next()?;
        let result_statement = BlockDeclaration{ source_context, declarations };
        Ok(ExactStructInnerDeclarationCase::create(current_parser, StructInnerDeclaration::BlockDeclaration(Box::new(result_statement))))
    }
    fn parse_templated_access_specifier_struct_inner_declaration(mut self, template_declaration: TemplateDeclaration, access_specifier: DeclarationAccessSpecifier) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        match statement_token {
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Type => Ok(self.parse_type_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            _ => Err(self.ctx.fail(format!("Expected data or nested struct declaration following template declaration and access specifier, got {}", statement_token))),
        }
    }
    fn parse_templated_struct_inner_declaration(self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        self.parse_template_declaration()?.flat_map_result(|mut parser, template_declaration| {
            let template_statement_token = parser.ctx.peek()?;
            let result_statement = match template_statement_token {
                // access specifiers
                CompilerToken::Public => parser.parse_templated_access_specifier_struct_inner_declaration(template_declaration, DeclarationAccessSpecifier::Public),
                CompilerToken::Internal => parser.parse_templated_access_specifier_struct_inner_declaration(template_declaration, DeclarationAccessSpecifier::Internal),
                CompilerToken::Local => parser.parse_templated_access_specifier_struct_inner_declaration(template_declaration, DeclarationAccessSpecifier::Local),
                // data and struct declarations
                CompilerToken::Constexpr => Ok(parser.parse_constexpr_statement(Some(template_declaration), None)?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
                CompilerToken::Type => Ok(parser.parse_type_statement(Some(template_declaration), None)?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
                CompilerToken::Struct => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
                CompilerToken::Class => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
                CompilerToken::Union => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
                _ => Err(parser.ctx.fail(format!("Expected access specifier, data or nested struct declaration following template declaration, got {}", template_statement_token))),
            }?;
            Ok(result_statement.to_parse_result())
        })?.disambiguate()
    }
    fn parse_empty_struct_inner_declaration(mut self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        let statement_token = self.ctx.next()?;
        self.ctx.check_token(statement_token, CompilerToken::Terminator)?;
        Ok(ExactStructInnerDeclarationCase::create(self, StructInnerDeclaration::EmptyDeclaration))
    }
    fn parse_access_specifier_struct_inner_declaration(mut self, access_specifier: DeclarationAccessSpecifier) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        match statement_token {
            // data and struct declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, Some(access_specifier))?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, Some(access_specifier))?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, Some(access_specifier))?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            _ => Err(self.ctx.fail(format!("Expected data or nested struct declaration following access specifier, got {}", statement_token))),
        }
    }
    fn parse_struct_inner_declaration(mut self) -> anyhow::Result<ExactStructInnerDeclarationCase<'a>> {
        let statement_token = self.ctx.peek()?;
        match statement_token {
            // template declaration
            CompilerToken::Template => self.parse_templated_struct_inner_declaration(),
            // access specifiers
            CompilerToken::Public => self.parse_access_specifier_struct_inner_declaration(DeclarationAccessSpecifier::Public),
            CompilerToken::Internal => self.parse_access_specifier_struct_inner_declaration(DeclarationAccessSpecifier::Internal),
            CompilerToken::Local => self.parse_access_specifier_struct_inner_declaration(DeclarationAccessSpecifier::Local),
            // data, struct, conditional, scope and blank declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, None)?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, None)?.map_data(|x| StructInnerDeclaration::DataDeclaration(Box::new(x)))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, None)?.map_data(|x| StructInnerDeclaration::NestedStructDeclaration(Box::new(x)))),
            CompilerToken::If => self.parse_struct_conditional_declaration(),
            CompilerToken::ScopeStart => self.parse_struct_block_declaration(),
            CompilerToken::Terminator => self.parse_empty_struct_inner_declaration(),
            // In all other cases assume it is a member declaration. Telling for sure is difficult because it can start with an arbitrary type expression
            _ => self.parse_struct_member_declaration(),
        }
    }
    fn parse_postfix_conditional_expression(mut self) -> anyhow::Result<ExactExpressionCase<'a>> {
        let conditional_statement_token = self.ctx.next()?;
        self.ctx.check_token(conditional_statement_token, CompilerToken::If)?;

        let condition_enter_bracket_token = self.ctx.next()?;
        self.ctx.check_token(condition_enter_bracket_token, CompilerToken::SubExpressionStart)?;

        Ok(self.parse_complete_expression()?
        .flat_map_result(|mut parser, expression| {
            let condition_exit_bracket_token = parser.ctx.next()?;
            parser.ctx.check_token(condition_exit_bracket_token, CompilerToken::SubExpressionEnd)?;
            Ok(AmbiguousExpression::unambiguous(parser, expression))
        })?.disambiguate()?)
    }
    fn parse_struct_statement(mut self, struct_kind: UserDefinedTypeKind, template_declaration: Option<TemplateDeclaration>, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactParseCase<'a, StructStatement>> {
        self.ctx.discard_next()?;
        let source_context = self.ctx.source_context();
        self.parse_optional_alignment_expression()?
        .map_result(|mut parser, alignment_expression| {
            let struct_name_token = parser.ctx.next()?;
            let name = parser.ctx.check_identifier(struct_name_token)?;

            // Parse base classes if the next token is a base class separator
            let scope_enter_or_base_class_separator = parser.ctx.next()?;
            if scope_enter_or_base_class_separator == CompilerToken::BaseClass && struct_kind == UserDefinedTypeKind::Union {
                Err(parser.ctx.fail("Union types cannot have base classes"))
            } else if scope_enter_or_base_class_separator == CompilerToken::BaseClass {
                Ok(parser.parse_ambiguous_expression_list_extended(CompilerToken::ScopeStart, |parser| {
                    let source_context = parser.ctx.source_context();
                    Ok(ExactParseCase::create(parser, (source_context, true)))
                }, |mut parser_case| {
                    if parser_case.parser.ctx.peek()? == CompilerToken::If {
                        let condition_expression = parser_case.parser.parse_postfix_conditional_expression()?;
                        Ok(condition_expression.map_data(|y| BaseClassDeclaration{type_expression: parser_case.data.1.unwrap(), condition_expression: Some(y), source_context: parser_case.data.0}))
                    } else {
                        Ok(parser_case.map_data(|x| BaseClassDeclaration{type_expression: x.1.unwrap(), condition_expression: None, source_context: x.0}))
                    }
                }, |x| x.type_expression.to_string())?
                .map_data(|base_class_expressions| {
                    (alignment_expression.clone(), name.clone(), base_class_expressions)
                }))
            } else {
                // Next token should be scope enter if it is not a base class separator
                parser.ctx.check_token(scope_enter_or_base_class_separator, CompilerToken::ScopeStart)?;
                Ok(AmbiguousParsingResult::unambiguous(parser, (alignment_expression, name, Vec::new())))
            }
        })?
        .flat_map_result(|parser, (alignment_expression, name, base_class_expressions)| {
            let mut declarations: Vec<StructInnerDeclaration> = Vec::new();

            // Parse struct statements until we encounter the scope exit token
            let mut current_parser = parser;
            while current_parser.ctx.peek()? != CompilerToken::ScopeEnd {
                let struct_inner_statement = current_parser.parse_struct_inner_declaration()?;
                declarations. push(struct_inner_statement.data);
                current_parser = struct_inner_statement.parser;
            }
            current_parser.ctx.discard_next()?;

            let terminator_token = current_parser.ctx.next()?;
            current_parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

            let result_statement = StructStatement{ source_context: source_context.clone(), template_declaration: template_declaration.clone(), access_specifier, struct_kind, alignment_expression, name: Some(name), base_class_expressions, declarations };
            Ok(AmbiguousParsingResult::unambiguous(current_parser, result_statement))
        })?.disambiguate()
    }
    fn parse_templated_access_specifier_namespace_level_statement(mut self, template_declaration: TemplateDeclaration, access_specifier: DeclarationAccessSpecifier) -> anyhow::Result<ExactNamespaceLevelDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        Ok(match statement_token {
            // data and struct declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            _ => Err(self.ctx.fail(format!("Expected data or struct declaration following template declaration and access specifier, got {}", statement_token))),
        }?)
    }
    fn parse_templated_namespace_level_statement(self) -> anyhow::Result<ExactNamespaceLevelDeclarationCase<'a>> {
        self.parse_template_declaration()?.flat_map_result(|mut parser, template_declaration| {
            let template_statement_token = parser.ctx.peek()?;
            Ok(match template_statement_token {
                // access specifiers
                CompilerToken::Public => parser.parse_templated_access_specifier_namespace_level_statement(template_declaration, DeclarationAccessSpecifier::Public),
                CompilerToken::Internal => parser.parse_templated_access_specifier_namespace_level_statement(template_declaration, DeclarationAccessSpecifier::Internal),
                CompilerToken::Local => parser.parse_templated_access_specifier_namespace_level_statement(template_declaration, DeclarationAccessSpecifier::Local),
                // data and struct declarations
                CompilerToken::Constexpr => Ok(parser.parse_constexpr_statement(Some(template_declaration), None)?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
                CompilerToken::Type => Ok(parser.parse_type_statement(Some(template_declaration), None)?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
                CompilerToken::Struct => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
                CompilerToken::Class => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
                CompilerToken::Union => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
                _ => Err(parser.ctx.fail(format!("Expected access access specifier, data or struct declaration following template declaration, got {}", template_statement_token))),
            }?.to_parse_result())
        })?.disambiguate()
    }
    fn parse_empty_namespace_level_statement(mut self) -> anyhow::Result<ExactNamespaceLevelDeclarationCase<'a>> {
        let statement_token = self.ctx.next()?;
        self.ctx.check_token(statement_token, CompilerToken::Terminator)?;
        Ok(ExactNamespaceLevelDeclarationCase::create(self, NamespaceLevelDeclaration::EmptyStatement))
    }
    fn parse_access_specifier_namespace_level_statement(mut self, access_specifier: DeclarationAccessSpecifier) -> anyhow::Result<ExactNamespaceLevelDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        match statement_token {
            // data, struct and namespace declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Namespace => Ok(self.parse_namespace_statement(Some(access_specifier))?.map_data(|x| NamespaceLevelDeclaration::NamespaceStatement(x))),
            _ => Err(self.ctx.fail(format!("Expected data or struct declaration following access specifier, got {}", statement_token))),
        }
    }
    fn parse_namespace_level_statement(mut self) -> anyhow::Result<ExactNamespaceLevelDeclarationCase<'a>> {
        let statement_token = self.ctx.peek()?;
        match statement_token {
            // template declaration
            CompilerToken::Template => self.parse_templated_namespace_level_statement(),
            // access specifiers
            CompilerToken::Public => self.parse_access_specifier_namespace_level_statement(DeclarationAccessSpecifier::Public),
            CompilerToken::Internal => self.parse_access_specifier_namespace_level_statement(DeclarationAccessSpecifier::Internal),
            CompilerToken::Local => self.parse_access_specifier_namespace_level_statement(DeclarationAccessSpecifier::Local),
            // data, struct, namespace and blank declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, None)?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, None)?.map_data(|x| NamespaceLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, None)?.map_data(|x| NamespaceLevelDeclaration::StructStatement(x))),
            CompilerToken::Namespace => Ok(self.parse_namespace_statement(None)?.map_data(|x| NamespaceLevelDeclaration::NamespaceStatement(x))),
            CompilerToken::Terminator => self.parse_empty_namespace_level_statement(),
            _ => Err(self.ctx.fail(format!("Expected empty statement, access specifier, namespace, data or struct declaration, got {}", statement_token))),
        }
    }
    fn parse_namespace_statement(mut self, access_specifier: Option<DeclarationAccessSpecifier>) -> anyhow::Result<ExactParseCase<'a, NamespaceStatement>> {
        let namespace_statement_token = self.ctx.next()?;
        self.ctx.check_token(namespace_statement_token, CompilerToken::Namespace)?;
        let source_context = self.ctx.source_context();
        
        let name = self.parse_partial_identifier()?;
        let scope_enter_token = self.ctx.next()?;
        self.ctx.check_token(scope_enter_token, CompilerToken::ScopeStart)?;

        let mut declarations: Vec<NamespaceLevelDeclaration> = Vec::new();
        let mut current_parser = self;
        while current_parser.ctx.peek()? != CompilerToken::ScopeEnd {
            let declaration = current_parser.parse_namespace_level_statement()?;
            declarations.push(declaration.data);
            current_parser = declaration.parser;
        }
        current_parser.ctx.discard_next()?;

        let terminator_token = current_parser.ctx.next()?;
        current_parser.ctx.check_token(terminator_token, CompilerToken::Terminator)?;

        let result_statement = NamespaceStatement{ source_context, access_specifier, name, declarations };
        Ok(ExactParseCase::create(current_parser, result_statement))
    }
    fn parse_empty_top_level_statement(mut self) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        let statement_token = self.ctx.next()?;
        self.ctx.check_token(statement_token, CompilerToken::Terminator)?;
        Ok(ExactModuleTopLevelDeclarationCase::create(self, ModuleTopLevelDeclaration::EmptyStatement))
    }
    fn parse_templated_access_specifier_top_level_statement(mut self, template_declaration: TemplateDeclaration, access_specifier: DeclarationAccessSpecifier)  -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        Ok(match statement_token {
            // data and struct declarations
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(Some(template_declaration), Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            _ => Err(self.ctx.fail(format!("Expected data or struct declaration following template declaration and access specifier, got {}", statement_token))),
        }?)
    }
    fn parse_templated_top_level_statement(self) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        self.parse_template_declaration()?.flat_map_result(|mut parser, template_declaration| {
            let template_statement_token = parser.ctx.peek()?;
            Ok(match template_statement_token {
                // access specifiers
                CompilerToken::Public => parser.parse_templated_access_specifier_top_level_statement(template_declaration, DeclarationAccessSpecifier::Public),
                CompilerToken::Internal => parser.parse_templated_access_specifier_top_level_statement(template_declaration, DeclarationAccessSpecifier::Internal),
                CompilerToken::Local => parser.parse_templated_access_specifier_top_level_statement(template_declaration, DeclarationAccessSpecifier::Local),
                // data and struct declarations
                CompilerToken::Constexpr => Ok(parser.parse_constexpr_statement(Some(template_declaration), None)?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
                CompilerToken::Type => Ok(parser.parse_type_statement(Some(template_declaration), None)?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
                CompilerToken::Struct => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Struct, Some(template_declaration), None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
                CompilerToken::Class => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Class, Some(template_declaration), None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
                CompilerToken::Union => Ok(parser.parse_struct_statement(UserDefinedTypeKind::Union, Some(template_declaration), None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
                _ => Err(parser.ctx.fail(format!("Expected access specifier, data or struct declaration following template declaration, got {}", template_statement_token))),
            }?.to_parse_result())
        })?.disambiguate()
    }
    fn parse_access_specifier_top_level_statement(mut self, access_specifier: DeclarationAccessSpecifier) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        // discard access specifier token
        self.ctx.discard_next()?;
        let statement_token = self.ctx.peek()?;
        match statement_token {
            CompilerToken::Input => self.parse_input_statement(Some(access_specifier)),
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Namespace => Ok(self.parse_namespace_statement(Some(access_specifier))?.map_data(|x| ModuleTopLevelDeclaration::NamespaceStatement(x))),
            _ => Err(self.ctx.fail(format!("Expected extern, data or struct declaration following access specifier, got {}", statement_token))),
        }
    }
    fn parse_top_level_statement(mut self) -> anyhow::Result<ExactModuleTopLevelDeclarationCase<'a>> {
        let statement_token = self.ctx.peek()?;
        match statement_token {
            // template declaration
            CompilerToken::Template => self.parse_templated_top_level_statement(),
            // access specifiers
            CompilerToken::Public => self.parse_access_specifier_top_level_statement(DeclarationAccessSpecifier::Public),
            CompilerToken::Internal => self.parse_access_specifier_top_level_statement(DeclarationAccessSpecifier::Internal),
            CompilerToken::Local => self.parse_access_specifier_top_level_statement(DeclarationAccessSpecifier::Local),
            // import, extern, data, struct, namespace or blank declarations
            CompilerToken::Import => self.parse_import_statement(),
            CompilerToken::Input => self.parse_input_statement(None),
            CompilerToken::Constexpr => Ok(self.parse_constexpr_statement(None, None)?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Type => Ok(self.parse_type_statement(None, None)?.map_data(|x| ModuleTopLevelDeclaration::DataStatement(x))),
            CompilerToken::Struct => Ok(self.parse_struct_statement(UserDefinedTypeKind::Struct, None, None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Class => Ok(self.parse_struct_statement(UserDefinedTypeKind::Class, None, None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Union => Ok(self.parse_struct_statement(UserDefinedTypeKind::Union, None, None)?.map_data(|x| ModuleTopLevelDeclaration::StructStatement(x))),
            CompilerToken::Namespace => Ok(self.parse_namespace_statement(None)?.map_data(|x| ModuleTopLevelDeclaration::NamespaceStatement(x))),
            CompilerToken::Terminator => self.parse_empty_top_level_statement(),
            _ => Err(self.ctx.fail(format!("Expected access specifier, import, template, data or struct declaration, got {}", statement_token))),
        }
    }
    fn parse_source_file(self) -> anyhow::Result<ModuleSourceFile> {
        let mut declarations: Vec<ModuleTopLevelDeclaration> = Vec::new();
        let mut current_parser = self;
        while current_parser.ctx.peek_or_eof()?.is_some() {
            let declaration = current_parser.parse_top_level_statement()?;
            declarations.push(declaration.data);
            current_parser = declaration.parser;
        }
        Ok(ModuleSourceFile{ file_name: current_parser.ctx.file_name.to_string(), declarations })
    }
    fn parse_single_expression(self) -> anyhow::Result<Expression> {
        Ok(self.parse_complete_expression()?.flat_map_result(|mut parser, expression| {
            let next_token_or_eof = parser.ctx.next_or_eof()?;
            if next_token_or_eof != None {
                Err(parser.ctx.fail(format!("Did not consume all input: expected <EOF>, got {}", next_token_or_eof.unwrap())))
            } else {
                Ok(AmbiguousParsingResult::unambiguous(parser, expression))
            }
        })?.disambiguate()?.data)
    }
    fn parse_single_statement(self) -> anyhow::Result<Statement> {
        Ok(self.parse_statement()?.map_result(|mut parser, statement| {
            let next_token_or_eof = parser.ctx.next_or_eof()?;
            if next_token_or_eof != None {
                Err(parser.ctx.fail(format!("Did not consume all input: expected <EOF>, got {}", next_token_or_eof.unwrap())))
            } else {
                Ok(statement)
            }
        })?)
    }
    fn unary_operator_to_source_text(operator: UnaryOperator) -> (&'static str, bool, bool, bool) {
        match operator {
            UnaryOperator::StructMakePointer => ("*", true, true, true),
            UnaryOperator::ArithmeticNegate => ("-", false, false, false),
            UnaryOperator::BitwiseInverse => ("~", false, false, false),
            UnaryOperator::BoolNegate => ("!", false, false, false),
            UnaryOperator::StructAlignOf => ("alignof", false, false, false),
            UnaryOperator::StructSizeOf => ("sizeof", false, false, false),
        }
    }
    fn unary_expression_to_source_text(expression: &UnaryExpression) -> String {
        let (operator_source_text, wrap_operator, wrap_expression, operator_after_expression) = Self::unary_operator_to_source_text(expression.operator);

        let mut result_builder = String::with_capacity(20);
        if wrap_operator { result_builder.push('('); }
        if !operator_after_expression { result_builder.push_str(operator_source_text); }

        if wrap_expression { result_builder.push('('); }
        result_builder.push_str(Self::expression_to_source_text(&expression.expression).as_str());
        if wrap_expression { result_builder.push(')'); }

        if operator_after_expression { result_builder.push_str(operator_source_text); }
        if wrap_operator { result_builder.push(')'); }
        result_builder
    }
    fn array_index_expression_to_source_text(expression: &ArrayTypeExpression) -> String {
        let mut result_builder = Self::expression_to_source_text(&expression.element_type_expression);
        result_builder.push('[');
        result_builder.push_str(Self::expression_to_source_text(&expression.array_length_expression).as_str());
        result_builder.push(']');
        result_builder
    }
    fn partial_identifier_to_source_text(identifier: &PartialIdentifier) -> String {
        let mut result_builder = String::with_capacity(20);
        if identifier.kind == PartialIdentifierKind::Absolute {
            result_builder.push_str("::");
        } else if identifier.kind == PartialIdentifierKind::ModuleRelative {
            result_builder.push_str("module::");
        }
        result_builder.push_str(identifier.path.join("::").as_str());
        result_builder
    }
    fn integer_constant_to_source_text(constant: i32) -> String {
        constant.to_string()
    }
    fn conditional_expression_to_source_text(expression: &ConditionalExpression) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("if (");
        result_builder.push_str(Self::expression_to_source_text(&expression.condition_expression).as_str());
        result_builder.push_str(") ");
        result_builder.push_str(Self::expression_to_source_text(&expression.true_expression).as_str());
        result_builder.push_str(" else ");
        result_builder.push_str(&Self::expression_to_source_text(&expression.false_expression).as_str());
        result_builder
    }
    fn delimited_expression_list_to_source_text(expressions: &Vec<Expression>) -> String {
        let expressions_source_text: Vec<String> = expressions.iter().map(|x| Self::expression_to_source_text(x)).collect();
        expressions_source_text.join(", ")
    }
    fn expression_value_type_to_source_text(value_type: ExpressionValueType, alt_form: bool) -> &'static str {
        match value_type {
            ExpressionValueType::Int => "int",
            ExpressionValueType::Typename => if alt_form { "type" } else { "typename" },
            ExpressionValueType::Closure => "@closure",
            ExpressionValueType::MetaStruct => "@metastruct",
        }
    }
    fn member_access_expression_to_source_text(expression: &MemberAccessExpression) -> String {
        let mut result_builder = Self::expression_to_source_text(&expression.type_expression);
        result_builder.push_str("::");
        result_builder.push_str(Self::expression_value_type_to_source_text(expression.member_type, false));
        result_builder.push(' ');
        result_builder.push_str(expression.member_name.as_str());
        if let Some(argument_expressions) = &expression.template_arguments {
            result_builder.push('<');
            result_builder.push_str(Self::delimited_expression_list_to_source_text(argument_expressions).as_str());
            result_builder.push_str(">");
        }
        result_builder
    }
    fn binary_operator_to_source_text(operator: BinaryOperator) -> &'static str {
        match operator {
            BinaryOperator::LogicalLess => "<",
            BinaryOperator::LogicalLessEquals => "<=",
            BinaryOperator::LogicalMore => ">",
            BinaryOperator::LogicalMoreEquals => ">=",
            BinaryOperator::ShortCircuitAnd => "&&",
            BinaryOperator::ShortCircuitOr => "||",
            BinaryOperator::Equals => "==",
            BinaryOperator::NotEquals => "!=",
            BinaryOperator::BitwiseShiftLeft => "<<",
            BinaryOperator::BitwiseShiftRight => ">>",
            BinaryOperator::BitwiseAnd => "&",
            BinaryOperator::BitwiseOr => "|",
            BinaryOperator::BitwiseXor => "^",
            BinaryOperator::ArithmeticAdd => "+",
            BinaryOperator::ArithmeticSubtract => "-",
            BinaryOperator::ArithmeticMultiply => "*",
            BinaryOperator::ArithmeticDivide => "/",
            BinaryOperator::ArithmeticRemainder => "%",
        }
    }
    fn access_specifier_to_source_text(access_specifier: DeclarationAccessSpecifier) -> &'static str {
        match access_specifier {
            DeclarationAccessSpecifier::Public => "pub",
            DeclarationAccessSpecifier::Internal => "internal",
            DeclarationAccessSpecifier::Local => "local",
        }
    }
    fn binary_expression_to_source_text(expression: &BinaryExpression) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("(");
        result_builder.push_str(Self::expression_to_source_text(&expression.left_expression).as_str());
        result_builder.push_str(" ");
        result_builder.push_str(Self::binary_operator_to_source_text(expression.operator));
        result_builder.push_str(" ");
        result_builder.push_str(Self::expression_to_source_text(&expression.right_expression).as_str());
        result_builder.push_str(")");
        result_builder
    }
    fn while_loop_statement_to_source_text(statement: &WhileLoopStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("while (");
        result_builder.push_str(Self::expression_to_source_text(&statement.condition_expression).as_str());
        result_builder.push_str(") ");
        result_builder.push_str(Self::statement_to_source_text(&statement.loop_body_statement).as_str());
        result_builder
    }
    fn assignment_statement_to_source_text(statement: &AssignmentStatement) -> String {
        let mut result_builder = Self::expression_to_source_text(&statement.left_hand_expression);
        result_builder.push(' ');
        if statement.assignment_operator.is_some() {
            result_builder.push_str(Self::binary_operator_to_source_text(statement.assignment_operator.unwrap()));
        }
        result_builder.push_str("= ");
        result_builder.push_str(Self::expression_to_source_text(&statement.assignment_expression).as_str());
        result_builder.push(';');
        result_builder
    }
    fn conditional_statement_to_source_text(statement: &ConditionalStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("if (");
        result_builder.push_str(Self::expression_to_source_text(&statement.condition_expression).as_str());
        result_builder.push_str(") ");
        result_builder.push_str(Self::statement_to_source_text(&statement.then_statement).as_str());
        if statement.else_statement.is_some() {
            result_builder.push_str(" else ");
            result_builder.push_str(Self::statement_to_source_text(statement.else_statement.as_ref().unwrap()).as_str());
        }
        result_builder
    }
    fn declaration_statement_to_source_text(statement: &DeclarationStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str(Self::expression_value_type_to_source_text(statement.value_type, false));
        result_builder.push(' ');
        result_builder.push_str(statement.name.as_str());
        if statement.initializer.is_some() {
            result_builder.push_str(" = ");
            result_builder.push_str(Self::expression_to_source_text(statement.initializer.as_ref().unwrap()).as_str());
        }
        result_builder.push(';');
        result_builder
    }
    fn block_statement_to_source_text(statement: &BlockStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("{ ");
        for statement in &statement.statements {
            result_builder.push_str(Self::statement_to_source_text(statement).as_str());
            result_builder.push(' ');
        }
        result_builder.push_str("}");
        result_builder
    }
    fn statement_to_source_text(statement: &Statement) -> String {
        match statement {
            Statement::WhileLoopStatement(statement_inner) => Self::while_loop_statement_to_source_text(&**statement_inner),
            Statement::AssignmentStatement(statement_inner) => Self::assignment_statement_to_source_text(&**statement_inner),
            Statement::ConditionalStatement(statement_inner) => Self::conditional_statement_to_source_text(&**statement_inner),
            Statement::DeclarationStatement(statement_inner) => Self::declaration_statement_to_source_text(&**statement_inner),
            Statement::BlockStatement(statement_inner) => Self::block_statement_to_source_text(&**statement_inner),
            Statement::ContinueLoopStatement(_) => "continue;".to_string(),
            Statement::BreakLoopStatement(_) => "break;".to_string(),
            Statement::EmptyStatement(_) => ";".to_string(),
        }
    }
    fn block_expression_to_source_text(expression: &BlockExpression) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("{ ");
        for statement in &expression.statements {
            result_builder.push_str(Self::statement_to_source_text(statement).as_str());
            result_builder.push(' ');
        }
        result_builder.push_str(Self::expression_to_source_text(&expression.return_value_expression).as_str());
        result_builder.push_str("}");
        result_builder
    }
    fn struct_declaration_expression_to_source_text(expression: &StructStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("struct { ");
        for declaration in &expression.declarations {
            result_builder.push_str(Self::struct_inner_declaration_to_source_text(declaration).as_str());
            result_builder.push(' ');
        }
        result_builder.push_str("}");
        result_builder
    }
    fn identifier_expression_to_source_text(expression: &IdentifierExpression) -> String {
        let mut result_builder = Self::partial_identifier_to_source_text(&expression.identifier);
        if let Some(argument_expressions) = &expression.template_arguments {
            result_builder.push('<');
            result_builder.push_str(Self::delimited_expression_list_to_source_text(argument_expressions).as_str());
            result_builder.push_str(">");
        }
        result_builder
    }
    fn builtin_expression_to_source_text(expression: &BuiltinIdentifierExpression) -> String {
        match expression.identifier {
            BuiltinIdentifier::AddressSize => String::from("__address_size"),
            BuiltinIdentifier::TargetPlatform => String::from("__target_platform"),
            BuiltinIdentifier::TargetArch => String::from("__target_arch"),
        }
    }
    fn primitive_type_expression_to_source_text(expression: &PrimitiveTypeExpression) -> String {
        match expression.primitive_type {
            PrimitiveType::Void => String::from("void"),
            PrimitiveType::Char => String::from("char"),
            PrimitiveType::UnsignedChar => String::from("unsigned char"),
            PrimitiveType::WideChar => String::from("wchar_t"),
            PrimitiveType::ShortInt => String::from("short int"),
            PrimitiveType::UnsignedShortInt => String::from("unsigned short int"),
            PrimitiveType::Int => String::from("int"),
            PrimitiveType::UnsignedInt => String::from("unsigned int"),
            PrimitiveType::Float => String::from("float"),
            PrimitiveType::Double => String::from("double"),
            PrimitiveType::Bool => String::from("bool"),
            PrimitiveType::LongInt => String::from("long int"),
            PrimitiveType::UnsignedLongInt => String::from("unsigned long int"),
            PrimitiveType::LongLongInt => String::from("long long int"),
            PrimitiveType::UnsignedLongLongInt => String::from("unsigned long long int"),
            PrimitiveType::Char8 => String::from("char8_t"),
            PrimitiveType::Char16 => String::from("char16_t"),
            PrimitiveType::Char32 => String::from("char32_t"),
        }
    }
    fn cv_qualified_expression_to_source_text(expression: &CVQualifiedExpression) -> String {
        let mut result_builder = String::with_capacity(50);
        result_builder.push_str(Self::expression_to_source_text(&expression.base_expression).as_str());
        if expression.constant { result_builder.push_str(" const"); }
        if expression.volatile { result_builder.push_str(" volatile"); }
        result_builder
    }
    fn expression_to_source_text(expression: &Expression) -> String {
        match expression {
            Expression::UnaryExpression(expr) => Self::unary_expression_to_source_text(&**expr),
            Expression::ArrayIndexExpression(expr) => Self::array_index_expression_to_source_text(&**expr),
            Expression::IdentifierExpression(expr) => Self::identifier_expression_to_source_text(&**expr),
            Expression::IntegerConstantExpression(expr) => Self::integer_constant_to_source_text(expr.constant_value),
            Expression::ConditionalExpression(expr) => Self::conditional_expression_to_source_text(&**expr),
            Expression::MemberAccessExpression(expr) => Self::member_access_expression_to_source_text(&**expr),
            Expression::BinaryExpression(expr) => Self::binary_expression_to_source_text(&**expr),
            Expression::BlockExpression(expr) => Self::block_expression_to_source_text(&**expr),
            Expression::StructDeclarationExpression(expr) => Self::struct_declaration_expression_to_source_text(&**expr),
            Expression::BuiltinIdentifierExpression(expr) => Self::builtin_expression_to_source_text(&**expr),
            Expression::PrimitiveTypeExpression(expr) => Self::primitive_type_expression_to_source_text(&**expr),
            Expression::CVQualifiedExpression(expr) => Self::cv_qualified_expression_to_source_text(&**expr),
        }
    }
    fn block_declaration_to_source_text(declaration: &BlockDeclaration) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("{ ");
        for declaration in &declaration.declarations {
            result_builder.push_str(Self::struct_inner_declaration_to_source_text(declaration).as_str());
            result_builder.push(' ');
        }
        result_builder.push_str("}");
        result_builder
    }
    fn conditional_declaration_to_source_text(declaration: &ConditionalDeclaration) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("if (");
        result_builder.push_str(Self::expression_to_source_text(&declaration.condition_expression).as_str());
        result_builder.push_str(") ");
        result_builder.push_str(Self::struct_inner_declaration_to_source_text(&declaration.then_branch).as_str());
        if declaration.else_branch.is_some() {
            result_builder.push_str(" else ");
            result_builder.push_str(Self::struct_inner_declaration_to_source_text(declaration.else_branch.as_ref().unwrap()).as_str());
        }
        result_builder
    }
    fn member_declaration_to_source_text(declaration: &MemberDeclaration) -> String {
        let mut result_builder = String::with_capacity(20);
        if declaration.alignment_expression.is_some() {
            result_builder.push_str("alignas(");
            result_builder.push_str(Self::expression_to_source_text(declaration.alignment_expression.as_ref().unwrap()).as_str());
            result_builder.push_str(") ");
        }
        result_builder.push_str(Self::expression_to_source_text(&declaration.member_type_expression).as_str());
        result_builder.push(' ');
        result_builder.push_str(declaration.name.as_str());
        if declaration.array_size_expression.is_some() {
            result_builder.push_str("[");
            result_builder.push_str(Self::expression_to_source_text(declaration.array_size_expression.as_ref().unwrap()).as_str());
            result_builder.push_str("]");
        } else if declaration.bitfield_width_expression.is_some() {
            result_builder.push_str(": ");
            result_builder.push_str(Self::expression_to_source_text(declaration.bitfield_width_expression.as_ref().unwrap()).as_str());
        }
        result_builder.push(';');
        result_builder
    }
    fn template_declaration_to_source_text(declaration: &TemplateDeclaration) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("template<");
        let argument_strings: Vec<String> = declaration.arguments.iter().map(|x| {
            if x.default_value.is_some() {
                format!("{} {} = ({})", Self::expression_value_type_to_source_text(x.value_type, false), x.name.as_str(),
                    Self::expression_to_source_text(x.default_value.as_ref().unwrap()))
            } else {
                format!("{} {}", Self::expression_value_type_to_source_text(x.value_type, false), x.name.as_str())
            }
        }).collect();
        result_builder.push_str(argument_strings.join(", ").as_str());
        result_builder.push('>');
        result_builder
    }
    fn data_statement_to_source_text(statement: &DataStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        if statement.template_declaration.is_some() {
            result_builder.push_str(Self::template_declaration_to_source_text(statement.template_declaration.as_ref().unwrap()).as_str());
            result_builder.push(' ');
        }
        if let Some(access_specifier) = statement.access_specifier {
            result_builder.push_str(Self::access_specifier_to_source_text(access_specifier));
            result_builder.push(' ');
        }
        result_builder.push_str(Self::expression_value_type_to_source_text(statement.value_type, true));
        result_builder.push(' ');
        result_builder.push_str(statement.name.as_str());
        result_builder.push_str(" = ");
        result_builder.push_str(Self::expression_to_source_text(&statement.initializer).as_str());
        result_builder.push(';');
        result_builder
    }
    fn struct_inner_declaration_to_source_text(declaration: &StructInnerDeclaration) -> String {
        match declaration {
            StructInnerDeclaration::BlockDeclaration(inner_declaration) => Self::block_declaration_to_source_text(&**inner_declaration),
            StructInnerDeclaration::ConditionalDeclaration(inner_declaration) => Self::conditional_declaration_to_source_text(&**inner_declaration),
            StructInnerDeclaration::MemberDeclaration(inner_declaration) => Self::member_declaration_to_source_text(&**inner_declaration),
            StructInnerDeclaration::DataDeclaration(inner_declaration) => Self::data_statement_to_source_text(&**inner_declaration),
            StructInnerDeclaration::NestedStructDeclaration(inner_declaration) => Self::struct_statement_to_source_text(&**inner_declaration),
            StructInnerDeclaration::EmptyDeclaration => ";".to_string(),
        }
    }
    fn postfix_conditional_expression_to_source_text(expression: &Expression) -> String {
        let mut result_builder = String::with_capacity(50);
        result_builder.push_str("if (");
        result_builder.push_str(Self::expression_to_source_text(expression).as_str());
        result_builder.push_str(")");
        result_builder
    }
    fn base_class_declaration_to_source_text(base_class: &BaseClassDeclaration) -> String {
        let mut result_builder = String::with_capacity(50);
        result_builder.push_str(Self::expression_to_source_text(&base_class.type_expression).as_str());
        if let Some(conditional_expression) = &base_class.condition_expression {
            result_builder.push_str(" ");
            result_builder.push_str(Self::postfix_conditional_expression_to_source_text(conditional_expression).as_str());
        }
        result_builder
    }
    fn struct_statement_to_source_text(statement: &StructStatement) -> String {
        let mut result_builder = String::with_capacity(50);
        if statement.template_declaration.is_some() {
            result_builder.push_str(Self::template_declaration_to_source_text(statement.template_declaration.as_ref().unwrap()).as_str());
            result_builder.push(' ');
        }
        if let Some(access_specifier) = statement.access_specifier {
            result_builder.push_str(Self::access_specifier_to_source_text(access_specifier));
            result_builder.push(' ');
        }
        result_builder.push_str("struct ");
        if statement.alignment_expression.is_some() {
            result_builder.push_str("alignas(");
            result_builder.push_str(Self::expression_to_source_text(statement.alignment_expression.as_ref().unwrap()).as_str());
            result_builder.push_str(") ");
        }
        result_builder.push_str(statement.name.as_ref().map(|x| x.as_str()).unwrap_or("<unnamed struct>"));
        if !statement.base_class_expressions.is_empty() {
            result_builder.push_str(" : ");
            let expressions_source_text: Vec<String> = statement.base_class_expressions.iter().map(|x| Self::base_class_declaration_to_source_text(x)).collect();
            result_builder.push_str(expressions_source_text.join(", ").as_str());
        }
        result_builder.push_str(" { ");
        for declaration in &statement.declarations {
            result_builder.push_str(Self::struct_inner_declaration_to_source_text(declaration).as_str());
            result_builder.push(' ');
        }
        result_builder.push_str("};");
        result_builder
    }
    fn namespace_level_declaration_to_source_text(declaration: &NamespaceLevelDeclaration) -> String {
        match declaration {
            NamespaceLevelDeclaration::StructStatement(inner_declaration) => Self::struct_statement_to_source_text(inner_declaration),
            NamespaceLevelDeclaration::DataStatement(inner_declaration) => Self::data_statement_to_source_text(inner_declaration),
            NamespaceLevelDeclaration::NamespaceStatement(inner_declaration) => Self::namespace_statement_to_source_text(inner_declaration),
            NamespaceLevelDeclaration::EmptyStatement => ";".to_string(),
        }
    }
    fn namespace_statement_to_source_text(statement: &NamespaceStatement) -> String {
        let mut result_builder = String::with_capacity(50);
        if let Some(access_specifier) = statement.access_specifier {
            result_builder.push_str(Self::access_specifier_to_source_text(access_specifier));
            result_builder.push(' ');
        }
        result_builder.push_str("namespace ");
        result_builder.push_str(Self::partial_identifier_to_source_text(&statement.name).as_str());
        result_builder.push_str(" {\n");
        for declaration in &statement.declarations {
            result_builder.push_str(Self::namespace_level_declaration_to_source_text(declaration).as_str());
            result_builder.push_str("\n");
        }
        result_builder.push_str("};");
        result_builder
    }
    fn extern_statement_to_source_text(statement: &InputStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        if let Some(access_specifier) = statement.access_specifier {
            result_builder.push_str(Self::access_specifier_to_source_text(access_specifier));
            result_builder.push(' ');
        }
        result_builder.push_str("extern ");
        result_builder.push_str(Self::expression_value_type_to_source_text(statement.value_type, false));
        result_builder.push(' ');
        result_builder.push_str(statement.global_name.as_str());
        result_builder.push(';');
        result_builder
    }
    fn import_statement_to_source_text(statement: &ModuleImportStatement) -> String {
        let mut result_builder = String::with_capacity(20);
        result_builder.push_str("import ");
        match &statement.statement_type {
            ModuleImportStatementType::QualifiedImport(x) => {
                result_builder.push_str(Self::partial_identifier_to_source_text(x).as_str());
            }
            ModuleImportStatementType::CompositeImport(x) => {
                result_builder.push('{');
                result_builder.push_str(x.imported_names.join(", ").as_str());
                result_builder.push('}');
            }
        }
        result_builder.push(';');
        result_builder
    }
    fn module_top_level_declaration_to_source_text(declaration: &ModuleTopLevelDeclaration) -> String {
        match declaration {
            ModuleTopLevelDeclaration::StructStatement(inner_declaration) => Self::struct_statement_to_source_text(inner_declaration),
            ModuleTopLevelDeclaration::DataStatement(inner_declaration) => Self::data_statement_to_source_text(inner_declaration),
            ModuleTopLevelDeclaration::InputStatement(inner_declaration) => Self::extern_statement_to_source_text(inner_declaration),
            ModuleTopLevelDeclaration::ImportStatement(inner_declaration) => Self::import_statement_to_source_text(inner_declaration),
            ModuleTopLevelDeclaration::NamespaceStatement(inner_declaration) => Self::namespace_statement_to_source_text(inner_declaration),
            ModuleTopLevelDeclaration::EmptyStatement => ";".to_string(),
        }
    }
    fn module_source_file_to_source_text(source_file: &ModuleSourceFile) -> String {
        let mut result_builder = String::with_capacity(20);
        for declaration in &source_file.declarations {
            result_builder.push_str(Self::module_top_level_declaration_to_source_text(declaration).as_str());
            result_builder.push_str("\n");
        }
        result_builder
    }
}

/// Attempts to parse a source file. Returns a result with a source file AST or an error
pub fn parse_source_file(file_name: &str, contents: &str) -> anyhow::Result<ModuleSourceFile> {
    let processed_input = CompilerParserInstance::preprocess_input_text(contents)?;
    let parser = CompilerParserInstance { ctx: CompilerLexerContext{ file_name, lex: CompilerToken::lexer(&processed_input), buffered_next_token: None } };
    parser.parse_source_file()
}

/// Attempts to parse the provided contents as a single expression. This is useful for REPL support
pub fn parse_expression(file_name: &str, contents: &str) -> anyhow::Result<Expression> {
    let processed_input = CompilerParserInstance::preprocess_input_text(contents)?;
    let parser = CompilerParserInstance { ctx: CompilerLexerContext{ file_name, lex: CompilerToken::lexer(&processed_input), buffered_next_token: None } };
    parser.parse_single_expression()
}

/// Attempts to parse the provided contents as a single statement. This is useful for REPL support
pub fn parse_statement(file_name: &str, contents: &str) -> anyhow::Result<Statement> {
    let processed_input = CompilerParserInstance::preprocess_input_text(contents)?;
    let parser = CompilerParserInstance { ctx: CompilerLexerContext{ file_name, lex: CompilerToken::lexer(&processed_input), buffered_next_token: None } };
    parser.parse_single_statement()
}

impl Display for PartialIdentifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::partial_identifier_to_source_text(self))
    }
}
impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::expression_to_source_text(self))
    }
}
impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::statement_to_source_text(self))
    }
}
impl Display for StructInnerDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::struct_inner_declaration_to_source_text(self))
    }
}
impl Display for DataStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::data_statement_to_source_text(self))
    }
}
impl Display for BaseClassDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::base_class_declaration_to_source_text(self))
    }
}
impl Display for StructStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::struct_statement_to_source_text(self))
    }
}
impl Display for NamespaceStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::namespace_statement_to_source_text(self))
    }
}
impl Display for NamespaceLevelDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::namespace_level_declaration_to_source_text(self))
    }
}
impl Display for ModuleTopLevelDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::module_top_level_declaration_to_source_text(self))
    }
}
impl Display for ModuleSourceFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CompilerParserInstance::module_source_file_to_source_text(self))
    }
}
