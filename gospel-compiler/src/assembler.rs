use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use anyhow::{anyhow};
use logos::{Lexer, Logos};
use strum::Display;
use gospel_vm::bytecode::{GospelInstruction, GospelOpcode};
use gospel_vm::writer::{GospelJumpLabelFixup, GospelModuleVisitor, GospelSourceFunctionDefinition, GospelSourceObjectReference};
use std::str::FromStr;
use crate::lex_util::get_line_number_and_offset_from_index;

#[derive(Debug, Clone, PartialEq, Eq, Display)]
enum AssemblerIdentifier {
    #[strum(to_string = "{0}")]
    Local(String),
    #[strum(to_string = "{container_name}::{local_name}")]
    Qualified{container_name: String, local_name: String},
}

#[derive(Logos, Debug, Clone, PartialEq, Display)]
#[logos(skip r"[ \r\t\n\f\u{feff}]+")]
enum AssemblerToken {
    // Attributes
    // Top level specifiers
    #[token("function")]
    #[strum(to_string = "function")]
    FunctionSpecifier,
    #[token("global")]
    #[strum(to_string = "global")]
    GlobalVariableSpecifier,
    #[token("max_slots")]
    #[strum(to_string = "max_slots")]
    MaxSlotsSpecifier,
    // Scope delimiters and local delimiters
    #[token("{")]
    #[strum(to_string = "{")]
    EnterScope,
    #[token("}")]
    #[strum(to_string = "}}")]
    ExitScope,
    #[token(":")]
    #[strum(to_string = ":")]
    NameSeparator,
    #[token("->")]
    #[strum(to_string = "->")]
    ReturnValueSeparator,
    #[token(";")]
    #[strum(to_string = ";")]
    StatementSeparator,
    // Operators
    #[token("=")]
    #[strum(to_string = "=")]
    AssignmentOperator,
    #[token("platform")]
    #[strum(to_string = "platform")]
    PlatformConfigOperator,
    // Identifiers and literals
    #[regex("[A-Za-z_$@][A-Za-z0-9_$@]*(?:::[A-Za-z_$][A-Za-z0-9_$]*)?", parse_identifier)]
    #[strum(to_string = "identifier")]
    Identifier(AssemblerIdentifier),
    #[regex("-?(?:0x[A-Za-z0-9]+)|-?(?:(?:[1-9]+[0-9]*)|0)", parse_decimal_or_hex_integer_literal)]
    #[strum(to_string = "integer literal")]
    IntegerLiteral(i32),
    #[regex("(?:\"(?:[^\"\\\\]|(?:\\\\\")|(?:\\\\\\\\))*\")", parse_string_literal)]
    #[strum(to_string = "string literal")]
    StringLiteral(String),
}
fn parse_identifier(lex: &mut Lexer<AssemblerToken>) -> Option<AssemblerIdentifier> {
    let identifier_slice = lex.slice();
    if let Some(split_index) = identifier_slice.find("::") {
        let container_name = identifier_slice[0..split_index].to_string();
        let local_name = identifier_slice[(split_index + 2)..].to_string();
        Some(AssemblerIdentifier::Qualified {container_name, local_name})
    } else {
        Some(AssemblerIdentifier::Local(identifier_slice.to_string()))
    }
}
fn parse_string_literal(lex: &mut Lexer<AssemblerToken>) -> Option<String> {
    let raw_literal: &str = lex.slice();
    Some(raw_literal[1..(raw_literal.len() - 1)].replace("\\\\", "\\"))
}
fn parse_decimal_or_hex_integer_literal(lex: &mut Lexer<AssemblerToken>) -> Option<i32> {
    let mut string_slice: &str = lex.slice();
    let mut sign_multiplier = 1;
    if string_slice.starts_with('-') {
        string_slice = &string_slice[1..];
        sign_multiplier = -1;
    }
    if string_slice.starts_with("0x") {
        string_slice = &string_slice[2..];
        i32::from_str_radix(string_slice, 16).ok().map(|x| x * sign_multiplier)
    } else {
        i32::from_str_radix(string_slice, 10).ok().map(|x| x * sign_multiplier)
    }
}

struct GospelLexerContext<'a> {
    file_name: &'a str,
    lex: Lexer<'a, AssemblerToken>,
}
impl GospelLexerContext<'_> {
    fn fail<T: AsRef<str>>(&mut self, error: T) -> anyhow::Error {
        let start_offset = self.lex.span().start;
        let (line_number, line_offset) = get_line_number_and_offset_from_index(self.lex.source(), start_offset);
        let file_name = self.file_name.to_string();
        anyhow!("{} (file: {} line {} offset {})", error.as_ref(), file_name, line_number + 1, line_offset)
    }
    fn get_current_line_number(&self) -> usize {
        let start_offset = self.lex.span().start;
        let (line_number, _) = get_line_number_and_offset_from_index(self.lex.source(), start_offset);
        line_number
    }
    fn next_or_eof(&mut self) -> anyhow::Result<Option<AssemblerToken>> {
        if let Some(wrapped_token) = self.lex.next() {
            match wrapped_token {
                Ok(result) => Ok(Some(result)),
                Err(_) => Err(self.fail("Failed to parse next token"))
            }
        } else { Ok(None) }
    }
    fn next_checked(&mut self) -> anyhow::Result<AssemblerToken> {
        self.next_or_eof()?.ok_or_else(|| self.fail("Expected a token, received <EOF>"))
    }
    fn next_expect_token(&mut self, token: AssemblerToken) -> anyhow::Result<()> {
        let next_token = self.next_checked()?;
        if next_token != token {
            Err(self.fail(format!("Expected {}, got {}", token, next_token)))
        } else { Ok({}) }
    }
    fn next_identifier(&mut self) -> anyhow::Result<AssemblerIdentifier> {
        match self.next_checked()? {
            AssemblerToken::Identifier(value) => Ok(value),
            other => Err(self.fail(format!("Expected identifier, got {}", other)))
        }
    }
    fn expect_local_identifier(&mut self, identifier: AssemblerIdentifier) -> anyhow::Result<String> {
        if let AssemblerIdentifier::Local(local_identifier) = identifier {
            Ok(local_identifier)
        } else { Err(self.fail("Expected local identifier, got qualified identifier")) }
    }
    fn next_local_identifier(&mut self) -> anyhow::Result<String> {
        self.next_identifier().and_then(|x| self.expect_local_identifier(x))
    }
}

#[derive(Debug)]
struct FunctionCodeAssembler<'a> {
    module_name: String,
    global_variable_names: HashSet<String>,
    local_function_names: HashSet<String>,
    function_definition: &'a mut GospelSourceFunctionDefinition,
    local_variable_slots: HashMap<String, u32>,
    label_lookup: HashMap<String, u32>,
    label_fixups: HashMap<String, Vec<GospelJumpLabelFixup>>,
}
impl FunctionCodeAssembler<'_> {
    fn parse_code_instruction(&mut self, instruction_name: &str, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<u32> {
        let instruction_opcode: GospelOpcode = GospelOpcode::from_str(instruction_name)
            .map_err(|_| ctx.fail(format!("Unknown instruction opcode: {}", instruction_name)))?;
        let line_number = ctx.get_current_line_number();
        let mut current_token = start_token;
        let mut instruction_immediate_operands: Vec<u32> = Vec::new();

        // Parse provided immediate value tokens and try to encode them
        while current_token != AssemblerToken::StatementSeparator {
            let immediate_value: u32 = match &current_token {
                AssemblerToken::Identifier(identifier) => {
                    match identifier {
                        AssemblerIdentifier::Local(local_identifier) => {
                            // Local identifier can refer to a local variable, argument, label, or a global variable
                            if let Some(local_variable_slot_index) = self.local_variable_slots.get(local_identifier) {
                                *local_variable_slot_index
                            } else if let Some(label_instruction_index) = self.label_lookup.get(local_identifier) {
                                *label_instruction_index
                            } else if self.global_variable_names.contains(local_identifier) {
                                self.function_definition.add_string_reference_internal(local_identifier)
                            } else if self.local_function_names.contains(local_identifier) {
                                let function_reference = GospelSourceObjectReference{module_name: self.module_name.clone(), local_name: local_identifier.clone()};
                                self.function_definition.add_function_reference_internal(function_reference)
                            } else {
                                // Assume forward declared label reference
                                if !self.label_fixups.contains_key(local_identifier) {
                                    self.label_fixups.insert(local_identifier.clone(), Vec::new());
                                }
                                self.label_fixups.get_mut(local_identifier).unwrap().push(GospelJumpLabelFixup{
                                    instruction_index: self.function_definition.current_instruction_count(),
                                    operand_index: instruction_immediate_operands.len() as u32,
                                });
                                u32::MAX
                            }
                        }
                        AssemblerIdentifier::Qualified { container_name, local_name } => {
                            // Refers to a function
                            self.function_definition.add_function_reference_internal(GospelSourceObjectReference{module_name: container_name.clone(), local_name: local_name.clone()})
                        }
                    }
                }
                AssemblerToken::IntegerLiteral(integer_value) => {
                    // Integer literals are converted to immediate operands directly
                    *integer_value as u32
                }
                AssemblerToken::StringLiteral(string_literal) => {
                    // String literals are treated as string references
                    self.function_definition.add_string_reference_internal(string_literal)
                }
                AssemblerToken::FunctionSpecifier => {
                    let function_reference = match ctx.next_identifier()? {
                        AssemblerIdentifier::Local(name) => GospelSourceObjectReference{module_name: self.module_name.clone(), local_name: name},
                        AssemblerIdentifier::Qualified{container_name, local_name} => GospelSourceObjectReference{module_name: container_name, local_name}
                    };
                    self.function_definition.add_function_reference_internal(function_reference)
                }
                AssemblerToken::GlobalVariableSpecifier => {
                    let global_name = ctx.next_local_identifier()?;
                    self.function_definition.add_string_reference_internal(global_name.as_str())
                }
                other => {
                    return Err(ctx.fail(format!("Expected integer literal, string literal, identifier or address taken value as instruction immediate operand, got {}", other)))
                }
            };
            instruction_immediate_operands.push(immediate_value);
            current_token = ctx.next_checked()?;
        }

        // Add the resulting instruction with the immediate values
        let result_instruction = GospelInstruction::create(instruction_opcode, &instruction_immediate_operands)
            .map_err(|x| ctx.fail(x.to_string()))?;
        Ok(self.function_definition.add_instruction_internal(result_instruction, line_number as i32))
    }
    fn parse_function_statement(&mut self, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        let mut current_token = start_token;

        // First token could be instruction name or identifier, we cannot tell until we parse the next token
        let label_or_instruction_name = if let AssemblerToken::Identifier(identifier) = current_token {
            current_token = ctx.next_checked()?;
            ctx.expect_local_identifier(identifier)?
        } else {
            return Err(ctx.fail(format!("Expected identifier, got {}", current_token)))
        };
        let statement_label_name: Option<String>;
        let instruction_name: String;

        // If current token is a label separator, first identifier is a label, and next one is the instruction name
        if current_token == AssemblerToken::NameSeparator {
            statement_label_name = Some(label_or_instruction_name);
            instruction_name = ctx.next_local_identifier()?;
            current_token = ctx.next_checked()?;
        } else {
            statement_label_name = None;
            instruction_name = label_or_instruction_name;
        }

        let result_instruction_index = self.parse_code_instruction(&instruction_name, current_token, ctx)?;
        if let Some(jump_label_name) = statement_label_name {
            self.label_lookup.insert(jump_label_name.clone(), result_instruction_index);

            // Fixup instructions that might have been previously added that refer to this label
            if let Some(labels_pending_fixup) = self.label_fixups.remove(&jump_label_name) {
                for label_fixup in labels_pending_fixup {
                    self.function_definition.fixup_control_flow_instruction(label_fixup, result_instruction_index)?;
                }
            }
        }
        Ok({})
    }
}

pub struct GospelAssembler {
    visitor: Rc<RefCell<dyn GospelModuleVisitor>>,
    global_variable_names: HashSet<String>,
    local_function_names: HashSet<String>,
}
impl GospelAssembler {
    fn parse_function_definition(&mut self, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        let function_name = ctx.next_local_identifier()?;
        let module_name = self.visitor.borrow().module_name().ok_or_else(|| anyhow!("Cannot compile declarations for unknown module name"))?;
        let function_declaration = GospelSourceObjectReference{module_name: module_name.clone(), local_name: function_name.clone()};

        // Add function to the locally defined list for convenience
        self.local_function_names.insert(function_name.clone());
        
        // Next token will be either a terminator (in this case, this is a function declaration, or interface definition), or a scope enter
        // (in that case, this is a full function definition, and we need to assemble the function body)
        let scope_enter_or_terminator_token = ctx.next_checked()?;
        if scope_enter_or_terminator_token == AssemblerToken::StatementSeparator {
            return self.visitor.borrow_mut().declare_function(function_declaration)
                .map_err(|x| ctx.fail(x.to_string()))
        } else if scope_enter_or_terminator_token != AssemblerToken::MaxSlotsSpecifier {
            return Err(ctx.fail(format!("Expected ; or max_slots, got {}", scope_enter_or_terminator_token)))
        }

        // Parse max slots attribute and then the function body open bracket
        let slot_count_token = ctx.next_checked()?;
        let max_slot_count = if let AssemblerToken::IntegerLiteral(slot_count) = slot_count_token {
            slot_count as u32
        } else { return Err(ctx.fail(format!("Expected integer literal, got {}", slot_count_token))); };
        ctx.next_expect_token(AssemblerToken::EnterScope)?;

        // This is a function definition, parse the function body now
        let mut function_definition = GospelSourceFunctionDefinition::create(true, ctx.file_name.to_string());
        function_definition.num_slots = max_slot_count;
        let module_name = self.visitor.borrow().module_name().ok_or_else(|| anyhow!("Cannot compile declarations for unknown module name"))?;
        let mut function_assembler = FunctionCodeAssembler{
            module_name,
            global_variable_names: self.global_variable_names.clone(),
            local_function_names: self.local_function_names.clone(),
            function_definition: &mut function_definition,
            local_variable_slots: HashMap::new(),
            label_lookup: HashMap::new(),
            label_fixups: HashMap::new(),
        };

        // Parse function definition statements now until we reach the closing bracket
        let mut current_statement_token = ctx.next_checked()?;
        while current_statement_token != AssemblerToken::ExitScope {
            function_assembler.parse_function_statement(current_statement_token, ctx)?;
            current_statement_token = ctx.next_checked()?;
        }
        // Scope must be followed by top level statement separator
        ctx.next_expect_token(AssemblerToken::StatementSeparator)?;

        // Define the function finally
        self.visitor.borrow_mut().define_function(function_declaration, function_definition)
            .map_err(|x| ctx.fail(x.to_string()))
    }
    fn parse_global_declaration(&mut self, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        let global_variable_name = ctx.next_local_identifier()?;

        ctx.next_expect_token(AssemblerToken::AssignmentOperator)?;
        let next_token = ctx.next_checked()?;
        let default_value = if let AssemblerToken::IntegerLiteral(integer_default_value) = next_token {
            integer_default_value
        } else {
            return Err(ctx.fail(format!("Expected integer literal, got {}", next_token)));
        };

        // Should end with a statement terminator
        ctx.next_expect_token(AssemblerToken::StatementSeparator)?;
        self.global_variable_names.insert(global_variable_name.clone());

        self.visitor.borrow_mut().define_global(&global_variable_name, default_value)
            .map_err(|x| ctx.fail(x.to_string()))
    }
    fn parse_top_level_statement(&mut self, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        match start_token {
            AssemblerToken::FunctionSpecifier => self.parse_function_definition(ctx),
            AssemblerToken::GlobalVariableSpecifier => self.parse_global_declaration(ctx),
            _ => Err(ctx.fail(format!("Expected top level statement (function), got {}", start_token)))
        }
    }
    /// Creates an assembler instance that will assemble the files and forward the results to the provided visitor
    pub fn create(visitor: Rc<RefCell<dyn GospelModuleVisitor>>) -> Self {
        GospelAssembler{visitor, global_variable_names: HashSet::new(), local_function_names: HashSet::new()}
    }
    /// Assembles the provided source assembly file and writes results to the underlying writer
    pub fn assemble_file_contents(&mut self, file_name: &str, contents: &str) -> anyhow::Result<()> {
        let mut lex_context = GospelLexerContext{file_name, lex: AssemblerToken::lexer(contents)};

        let mut current_token = lex_context.next_or_eof()?;
        while current_token.is_some() {
            self.parse_top_level_statement(current_token.unwrap(), &mut lex_context)?;
            current_token = lex_context.next_or_eof()?;
        }
        Ok({})
    }
}
