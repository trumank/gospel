use std::collections::{HashMap, HashSet};
use anyhow::{anyhow};
use bitflags::{bitflags};
use logos::{Lexer, Logos};
use strum_macros::Display;
use gospel_vm::bytecode::{GospelInstruction, GospelOpcode};
use gospel_vm::gospel_type::{GospelPlatformConfigProperty, GospelValueType};
use gospel_vm::writer::{GospelContainerWriter, GospelSourceFunctionDefinition, GospelSourceFunctionReference, GospelSourceSlotBinding, GospelSourceStaticValue};
use std::str::FromStr;

#[derive(Logos, Debug, Clone, PartialEq, Display)]
#[logos(skip r"[ \r\t\n\f]+")]
enum AssemblerToken {
    // Attributes
    #[token("hidden")]
    #[strum(to_string = "hidden")]
    AttributeHidden,
    #[token("extern")]
    #[strum(to_string = "extern")]
    AttributeExtern,
    // Top level specifiers
    #[token("function")]
    #[strum(to_string = "function")]
    FunctionSpecifier,
    #[token("global")]
    #[strum(to_string = "global")]
    GlobalVariableSpecifier,
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
    #[token("&")]
    #[strum(to_string = "&")]
    AddressTakenOperator,
    #[token("platform")]
    #[strum(to_string = "platform")]
    PlatformConfigOperator,
    // Identifiers and literals
    #[regex("[A-Za-z_$][A-Za-z0-9_$]*", |lex| lex.slice().to_string())]
    #[strum(to_string = "identifier")]
    Identifier(String),
    #[regex("-?(?:0x[A-Za-z0-9]+)|(?:(?:[1-9]+[0-9]*)|0)", parse_decimal_or_hex_integer_literal)]
    #[strum(to_string = "integer literal")]
    IntegerLiteral(i32),
    #[regex("(?:\"(?:[^\"\\\\]|(?:\\\\\")|(?:\\\\\\\\))*\")", parse_string_literal)]
    #[strum(to_string = "string literal")]
    StringLiteral(String),
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
    fn get_line_number_and_offset_from_index(contents: &str, char_index: usize) -> (usize, usize) {
        let mut current_index: usize = 0;
        let mut current_line_number: usize = 0;
        let mut current_line_start_index: usize = 0;

        while current_index < contents.len() && current_index <= char_index {
            if contents.as_bytes()[current_index] == '\n' as u8 {
                current_line_start_index = current_index;
                current_line_number += 1;
            }
            current_index += 1;
        }
        (current_line_number, char_index - current_line_start_index)
    }
    fn fail<T: AsRef<str>>(&mut self, error: T) -> anyhow::Error {
        let start_offset = self.lex.span().start;
        let (line_number, line_offset) = Self::get_line_number_and_offset_from_index(self.lex.source(), start_offset);
        let file_name = self.file_name.to_string();
        anyhow!("{} (file: {} line {} offset {})", error.as_ref(), file_name, line_number + 1, line_offset)
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
    fn next_identifier(&mut self) -> anyhow::Result<String> {
        match self.next_checked()? {
            AssemblerToken::Identifier(value) => Ok(value),
            other => Err(self.fail(format!("Expected identifier, got {}", other)))
        }
    }
}

bitflags! {
    struct AssemblerAttributeList: u8 {
        const None = 0;
        const Hidden = 1 << 0;
        const Extern = 1 << 1;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ConstantSlotIdentifier {
    value_type: GospelValueType,
    binding: GospelSourceSlotBinding,
}

#[derive(Debug)]
struct FunctionCodeAssembler<'a> {
    global_variable_names: HashSet<String>,
    function_definition: &'a mut GospelSourceFunctionDefinition,
    argument_names: HashMap<String, u32>,
    local_variable_slots: HashMap<String, u32>,
    constant_slot_lookup: HashMap<ConstantSlotIdentifier, u32>,
    label_lookup: HashMap<String, u32>,
}
impl FunctionCodeAssembler<'_> {
    fn find_or_add_constant_slot(&mut self, slot_type: GospelValueType, binding: GospelSourceSlotBinding) -> anyhow::Result<u32> {
        let identifier = ConstantSlotIdentifier{value_type: slot_type, binding};
        if let Some(existing_slot_index) = self.constant_slot_lookup.get(&identifier) {
            return Ok(*existing_slot_index);
        }
        let new_slot_index = self.function_definition.add_slot(slot_type, identifier.binding.clone())?;
        self.constant_slot_lookup.insert(identifier, new_slot_index);
        Ok(new_slot_index)
    }
    fn find_or_add_argument_slot(&mut self, argument_index: u32) -> anyhow::Result<u32> {
        let argument_type = self.function_definition.get_argument_type_at_index(argument_index)
            .ok_or_else(|| anyhow!("Invalid argument index #{}", argument_index))?;
        self.find_or_add_constant_slot(argument_type, GospelSourceSlotBinding::ArgumentValue(argument_index))
    }
    fn find_or_add_global_slot(&mut self, global_variable_name: String) -> anyhow::Result<u32> {
        self.find_or_add_constant_slot(GospelValueType::Integer, GospelSourceSlotBinding::StaticValue(GospelSourceStaticValue::GlobalVariableValue(global_variable_name)))
    }
    fn parse_code_instruction(&mut self, instruction_name: &str, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<u32> {
        let instruction_opcode: GospelOpcode = GospelOpcode::from_str(instruction_name)?;

        let mut current_token = start_token;
        let mut instruction_immediate_operands: Vec<u32> = Vec::new();

        // Parse provided immediate value tokens and try to encode them
        while current_token != AssemblerToken::StatementSeparator {
            let immediate_value: u32 = match &current_token {
                AssemblerToken::Identifier(identifier) => {
                    // Identifier can refer to a local variable, argument, label, or a global variable
                    if let Some(local_variable_slot_index) = self.local_variable_slots.get(identifier) {
                        *local_variable_slot_index
                    } else if let Some(function_argument_index) = self.argument_names.get(identifier) {
                        self.find_or_add_argument_slot(*function_argument_index)?
                    } else if let Some(label_instruction_index) = self.label_lookup.get(identifier) {
                        *label_instruction_index
                    } else if self.global_variable_names.contains(identifier) {
                        self.find_or_add_global_slot(identifier.clone())?
                    } else {
                        return Err(ctx.fail(format!("Identifier {} does not name a local variable, function argument, label or a global variable", identifier)));
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
                AssemblerToken::AddressTakenOperator => {
                    // Address taken operator is a syntactic sugar that creates an anonymous slot populated with a static value and returns its index
                    let static_value_start_token = ctx.next_checked()?;
                    let static_value = GospelAssembler::parse_static_value_constant(static_value_start_token, ctx)?;
                    self.find_or_add_constant_slot(static_value.value_type(), GospelSourceSlotBinding::StaticValue(static_value))?
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
        Ok(self.function_definition.add_instruction_internal(result_instruction))
    }
    fn parse_slot_directive(&mut self, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<u32> {
        // Parse type of the slot as the first token
        let variable_type = GospelAssembler::parse_value_type_token(&start_token)
            .ok_or_else(|| ctx.fail(format!("Expected value type, got {}", start_token)))?;

        // Parse optional default value for slot, if it has been provided
        let mut next_token = ctx.next_checked()?;
        let mut slot_binding = GospelSourceSlotBinding::Uninitialized;

        if next_token != AssemblerToken::StatementSeparator {
            let static_value = GospelAssembler::parse_static_value_constant(next_token, ctx)?;
            slot_binding = GospelSourceSlotBinding::StaticValue(static_value);
            next_token = ctx.next_checked()?;
        }

        // Make sure the directive is terminated with the statement terminator
        if next_token != AssemblerToken::StatementSeparator {
            return Err(ctx.fail(format!("Expected ;, got {}", next_token)));
        }

        // Add the resulting slot with the provided binding
        self.function_definition.add_slot(variable_type, slot_binding)
    }
    fn parse_function_statement(&mut self, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        let mut current_token = start_token;

        // First token could be instruction name or identifier, we cannot tell until we parse the next token
        let label_or_instruction_name = if let AssemblerToken::Identifier(identifier) = current_token {
            current_token = ctx.next_checked()?;
            identifier
        } else {
            return Err(ctx.fail(format!("Expected identifier, got {}", current_token)))
        };
        let statement_label_name: Option<String>;
        let instruction_name: String;

        // If current token is a label separator, first identifier is a label, and next one is the instruction name
        if current_token == AssemblerToken::NameSeparator {
            statement_label_name = Some(label_or_instruction_name);
            instruction_name = ctx.next_identifier()?;
            current_token = ctx.next_checked()?;
        } else {
            statement_label_name = None;
            instruction_name = label_or_instruction_name;
        }

        // Slot is a built-in assembler directive used for creating function slots, it is not an actual instruction
        if instruction_name == "Slot" {
            let result_slot_index = self.parse_slot_directive(current_token, ctx)?;
            if let Some(slot_label_name) = statement_label_name {
                self.local_variable_slots.insert(slot_label_name, result_slot_index);
            }
        } else {
            // This is a normal instruction otherwise, potentially with some synthetic arguments
            let result_instruction_index = self.parse_code_instruction(&instruction_name, current_token, ctx)?;
            if let Some(jump_label_name) = statement_label_name {
                self.label_lookup.insert(jump_label_name, result_instruction_index);
            }
        }
        Ok({})
    }
}

#[derive(Debug)]
pub struct GospelAssembler<'a> {
    writer: &'a mut GospelContainerWriter,
    global_variable_names: HashSet<String>,
}
impl GospelAssembler<'_> {
    fn parse_value_type_token(token: &AssemblerToken) -> Option<GospelValueType> {
        if let AssemblerToken::Identifier(type_name) = token {
            GospelValueType::from_str(type_name.as_str()).ok()
        } else { None }
    }
    fn parse_attribute_list(start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<(AssemblerAttributeList, AssemblerToken)> {
        let mut attribute_list = AssemblerAttributeList::None;
        let mut current_token = start_token;
        loop {
            match current_token {
                AssemblerToken::AttributeHidden => { attribute_list |= AssemblerAttributeList::Hidden; }
                AssemblerToken::AttributeExtern => { attribute_list |= AssemblerAttributeList::Extern; }
                _ => { break; }
            };
            current_token = ctx.next_checked()?;
        }
        Ok((attribute_list, current_token))
    }
    fn parse_static_value_constant(start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<GospelSourceStaticValue> {
        match &start_token {
            AssemblerToken::IntegerLiteral(integer_value) => {
                // Integer literals map directly to static value integer literals
                Ok(GospelSourceStaticValue::Integer(*integer_value))
            }
            AssemblerToken::PlatformConfigOperator => {
                // Property from the platform config by the name
                let platform_config_property_name = ctx.next_identifier()?;
                let property: GospelPlatformConfigProperty = GospelPlatformConfigProperty::from_str(platform_config_property_name.as_str())?;
                Ok(GospelSourceStaticValue::PlatformConfigProperty(property))
            }
            AssemblerToken::GlobalVariableSpecifier => {
                // Global variable specifier, next identifier is a name of a local variable. It also functions as a pre-declaration
                let global_variable_name = ctx.next_identifier()?;
                Ok(GospelSourceStaticValue::GlobalVariableValue(global_variable_name))
            }
            AssemblerToken::FunctionSpecifier => {
                // Function specifier, next identifier is a function name. It also functions as a pre-declaration
                let function_name = ctx.next_identifier()?;
                // TODO: Only local functions can be referenced currently
                Ok(GospelSourceStaticValue::FunctionId(GospelSourceFunctionReference::LocalFunction {function_name}))
            }
            // TODO: There is currently no assembler syntax for creation of lazy values
            other => Err(ctx.fail(format!("Expected integer literal or platform, global or function specifier followed by name, got {}", other)))
        }
    }
    fn parse_function_definition(&mut self, ctx: &mut GospelLexerContext, attributes: AssemblerAttributeList) -> anyhow::Result<()> {
        if attributes.intersects(AssemblerAttributeList::Extern) {
            return Err(ctx.fail("Function definitions cannot be marked as extern"));
        }
        let is_function_hidden = attributes.intersects(AssemblerAttributeList::Hidden);
        let function_name = ctx.next_identifier()?;

        let mut function_definition = GospelSourceFunctionDefinition::create(&function_name, is_function_hidden);
        let mut argument_name_map: HashMap<String, u32> = HashMap::new();

        let mut current_argument_token = ctx.next_checked()?;
        while current_argument_token != AssemblerToken::ReturnValueSeparator {
            // This might be a named argument, attempt to parse the token as identifier
            let mut maybe_argument_name: Option<String> = None;
            if let AssemblerToken::Identifier(argument_name) = current_argument_token {
                maybe_argument_name = Some(argument_name);

                // Next token must be a label separator, followed by the argument type
                ctx.next_expect_token(AssemblerToken::NameSeparator)?;
                current_argument_token = ctx.next_checked()?;
            }

            // Current token should be an argument type
            let argument_type = Self::parse_value_type_token(&current_argument_token)
                .ok_or_else(|| ctx.fail(format!("Expected value type, got {}", current_argument_token)))?;
            current_argument_token = ctx.next_checked()?;
            let mut argument_default_value: Option<GospelSourceStaticValue> = None;

            // If we have a default value for this argument, parse it
            if current_argument_token == AssemblerToken::AssignmentOperator {
                let default_value_start_token = ctx.next_checked()?;
                let default_value = GospelAssembler::parse_static_value_constant(default_value_start_token, ctx)?;
                argument_default_value = Some(default_value);
                current_argument_token = ctx.next_checked()?;
            }
            let argument_index = function_definition.add_function_argument(argument_type, argument_default_value)?;
            if let Some(argument_name) = maybe_argument_name {
                argument_name_map.insert(argument_name, argument_index);
            }
        }

        // All functions must have a return value since all gospel functions are pure
        let return_value_token = ctx.next_checked()?;
        let return_value_type = Self::parse_value_type_token(&return_value_token)
            .ok_or_else(|| ctx.fail(format!("Expected value type, got {}", return_value_token)))?;
        function_definition.set_return_value_type(return_value_type);

        // Entering the function implementation scope
        ctx.next_expect_token(AssemblerToken::EnterScope)?;

        let mut function_assembler = FunctionCodeAssembler{
            global_variable_names: self.global_variable_names.clone(),
            function_definition: &mut function_definition,
            argument_names: argument_name_map,
            local_variable_slots: HashMap::new(),
            constant_slot_lookup: HashMap::new(),
            label_lookup: HashMap::new(),
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
        self.writer.define_function(function_definition)
    }
    fn parse_global_declaration(&mut self, ctx: &mut GospelLexerContext, attributes: AssemblerAttributeList) -> anyhow::Result<()> {
        if attributes.intersects(AssemblerAttributeList::Hidden) {
            return Err(ctx.fail("Global variable declarations cannot be marked as extern"));
        }
        let global_variable_name = ctx.next_identifier()?;
        let mut global_default_value: Option<i32> = None;

        // If global variable is not marked extern, we should parse a default value

        if !attributes.intersects(AssemblerAttributeList::Extern) {
            ctx.next_expect_token(AssemblerToken::AssignmentOperator)?;
            let next_token = ctx.next_checked()?;
            let static_value = Self::parse_static_value_constant(next_token, ctx)?;
            if let GospelSourceStaticValue::Integer(integer_default_value) = static_value {
                global_default_value = Some(integer_default_value);
            } else {
                return Err(ctx.fail("Global variable declarations can only have integer literals as default values"));
            }
        }
        // Should end with a statement terminator
        ctx.next_expect_token(AssemblerToken::StatementSeparator)?;

        self.global_variable_names.insert(global_variable_name.clone());
        self.writer.define_global(&global_variable_name, global_default_value)
    }
    fn parse_top_level_statement(&mut self, start_token: AssemblerToken, ctx: &mut GospelLexerContext) -> anyhow::Result<()> {
        let (attributes, top_level_token) = Self::parse_attribute_list(start_token, ctx)?;
        match top_level_token {
            AssemblerToken::FunctionSpecifier => self.parse_function_definition(ctx, attributes),
            AssemblerToken::GlobalVariableSpecifier => self.parse_global_declaration(ctx, attributes),
            _ => Err(ctx.fail(format!("Expected top level statement (function), got {}", top_level_token)))
        }
    }
    /// Creates an assembler instance that will assemble the files and write the results to the given writer
    pub fn create(writer: &mut GospelContainerWriter) -> GospelAssembler<'_> {
        GospelAssembler{writer, global_variable_names: HashSet::new()}
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
    /// Assembles the given input as a static value and returns it
    pub fn assemble_static_value(file_name: &str, contents: &str) -> anyhow::Result<GospelSourceStaticValue> {
        let mut lex_context = GospelLexerContext{file_name, lex: AssemblerToken::lexer(contents)};
        let start_token = lex_context.next_checked()?;
        Self::parse_static_value_constant(start_token, &mut lex_context)
    }
}
