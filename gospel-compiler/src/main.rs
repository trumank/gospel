use std::cell::RefCell;
use std::env::current_dir;
use std::fs::{create_dir_all, read, read_to_string, write};
use std::ops::Deref;
use std::path::{absolute, PathBuf};
use std::process::exit;
use std::rc::Rc;
use std::str::FromStr;
use anyhow::{anyhow};
use clap::{Args, Parser, ValueEnum};
use itertools::Itertools;
use gospel_compiler::assembler::disassemble_function;
use gospel_typelib::type_model::{ResolvedUDTMemberLayout, TargetTriplet, Type, TypeGraphLike, TypeLayoutCache, TypeTree};
use gospel_vm::module::{GospelContainer};
use gospel_vm::reader::GospelContainerReader;
use gospel_vm::vm::{GospelVMContainer, GospelVMOptions, GospelVMRunContext, GospelVMState, GospelVMTypeContainer, GospelVMValue};
use gospel_vm::writer::{GospelContainerBuilder, GospelContainerWriter};
use crate::assembler::GospelAssembler;
use crate::ast::ExpressionValueType;
use crate::backend::{CompilerInstance, CompilerModuleBuilder, CompilerOptions, CompilerResultTrait};
use crate::module_definition::{resolve_module_dependencies, GospelModule};
use crate::parser::{parse_expression, parse_source_file};

pub mod assembler;
pub mod ast;
pub mod parser;
mod lex_util;
pub mod backend;
pub mod module_definition;

#[derive(Parser, Debug)]
struct ActionAssembleModule {
    /// Name of the resulting module
    #[arg(index = 1)]
    module_name: String,
    /// Name of the container output file to write. Default is container_name.gso
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Assembly files to compile to the container
    #[arg(index = 2)]
    files: Vec<PathBuf>,
}

#[derive(Debug, Clone)]
struct GlobalVariable {
    name: String,
    value: u64,
}

impl FromStr for GlobalVariable {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name, value_str) = s.split_once('=')
            .ok_or_else(|| anyhow!("Global variable must be in format 'NAME=<value>'"))?;

        let value = if let Some(hex_str) = value_str.strip_prefix("0x").or_else(|| value_str.strip_prefix("0X")) {
            u64::from_str_radix(hex_str, 16).map(|v| v)
        } else {
            value_str.parse::<u64>()
        }.map_err(|_| anyhow!("Failed to parse {value_str} as int"))?;

        Ok(GlobalVariable { name: name.to_string(), value })
    }
}

/// Shared options passed to the Gospel VM
#[derive(Debug, Args)]
struct CommandLineVMOptions {
    /// Target triple to use as a platform config. When not provided, current platform will be used instead (environment is assumed to be native to the platform)
    #[arg(long, short)]
    target: Option<String>,
    /// Global variables to set (must be int) e.g. VERSION=12 or SIZE=0x10
    #[arg(long, short)]
    global: Vec<GlobalVariable>,
    /// Disable default target selection, when no target is provided code will run with no target triplet (and will not be able to calculate sizes)
    #[arg(long)]
    no_default_target: bool,
    /// Do not use default global variable values provided by the module containers
    #[arg(long)]
    no_default_globals: bool,
}
impl CommandLineVMOptions {
    fn create_run_context(&self) -> anyhow::Result<GospelVMRunContext> {
        let target_triplet = if let Some(target_triplet_name) = &self.target {
            Some(TargetTriplet::parse(target_triplet_name.as_str())
                .map_err(|x| anyhow!("Failed to parse provided target triplet: {}", x.to_string()))?)
        } else if !self.no_default_target {
            Some(TargetTriplet::current_target()
                .ok_or_else(|| anyhow!("Current platform is not a valid target. Please specify target manually with --target "))?)
        } else { None };

        let mut vm_options = GospelVMOptions::default();
        if let Some(set_target_triplet) = target_triplet {
            vm_options = vm_options.target_triplet(set_target_triplet);
        }
        for global in &self.global {
            vm_options = vm_options.with_global(&global.name, global.value);
        }
        if self.no_default_globals {
            vm_options = vm_options.no_default_globals();
        }
        Ok(GospelVMRunContext::create(vm_options))
    }
}

#[derive(Debug, Parser)]
struct ActionCallFunction {
    /// VM options to pass to the VM
    #[command(flatten)]
    vm_options: CommandLineVMOptions,
    /// Container files to load to the VM before evaluation of the expression
    #[arg(long, short)]
    input: Vec<PathBuf>,
    /// Name of the container to find the function in, if not provided all containers are searched in the same order they are passed on the command line
    #[arg(long, short)]
    container_name: Option<String>,
    /// Name of the function to call
    #[arg(index = 1)]
    function_name: String,
    /// Optional arguments to provide to the function
    #[arg(index = 2)]
    function_args: Vec<String>,
    /// Output format for the type tree (if result is a type tree)
    #[arg(long, short = 'f')]
    output_format: Option<TypeTreeOutputFormat>,
}

#[derive(Parser, Debug)]
struct ActionDisassembleModule {
    /// Module container to disassemble
    #[arg(index = 1)]
    input: PathBuf,
    /// Name of the function to disassemble. If not provided, all functions are disassembled
    #[arg(long, short)]
    function_name: Option<String>,
    /// Output to write the result disassembly to. If not provided, result is written to stdout
    #[arg(long, short)]
    output: Option<PathBuf>,
}

#[derive(Parser, Debug)]
struct ActionParseSourceFile {
    /// Path to the source file to parse
    #[arg(index = 1)]
    input: PathBuf,
    /// Output to write the result JSON to. If not provided, result is written to stdout
    #[arg(long, short)]
    output: Option<PathBuf>,
}

/// Shared options passed to the Gospel Compiler
#[derive(Debug, Args)]
struct CommandLineCompilerOptions {
    /// Whenever partial type definitions should be produced (wrap members in try/catch blocks)
    #[arg(long)]
    allow_partial_types: bool,
    /// Whenever prototype UDT layout metadata should be written
    #[arg(long)]
    generate_prototypes: bool,
    /// Whenever implicit integer narrowing conversions are allowed
    #[arg(long)]
    allow_implicit_narrowing: bool,
}
impl CommandLineCompilerOptions {
    fn create_compiler_instance(&self) -> anyhow::Result<Rc<CompilerInstance>> {
        let mut compiler_options = CompilerOptions::default();
        if self.allow_partial_types {
            compiler_options = compiler_options.allow_partial_types();
        }
        if self.generate_prototypes {
            compiler_options = compiler_options.generate_prototype_layouts();
        }
        if self.allow_implicit_narrowing {
            compiler_options = compiler_options.allow_implicit_narrowing_conversions();
        }
        Ok(CompilerInstance::create(compiler_options))
    }
}

/// Options passed to the compiler to compile a single module
#[derive(Debug, Args)]
struct CommandLineModuleCompileOptions {
    /// Additional module paths that should be included and available to the compiled module
    #[arg(long, short)]
    included_modules: Vec<PathBuf>,
    /// Module directory to compile. If not specified, current directory is used
    #[arg(index = 1)]
    module: Option<PathBuf>,
}
impl CommandLineModuleCompileOptions {
    fn resolve_module_dependencies(&self) -> anyhow::Result<Rc<GospelModule>> {
        let mut all_module_paths: Vec<PathBuf> = Vec::new();
        for module_include_path in &self.included_modules {
            let absolute_module_path = absolute(module_include_path)?;
            if !all_module_paths.contains(&absolute_module_path) {
                all_module_paths.push(absolute_module_path);
            }
        }
        let absolute_module_path = absolute(if let Some(user_specified_path) = self.module.clone() {
            user_specified_path
        } else { current_dir()? })?;
        let main_module_index = all_module_paths.iter().position(|x| x == &absolute_module_path).unwrap_or_else(|| {
            all_module_paths.push(absolute_module_path);
            all_module_paths.len() - 1
        });
        let resolved_modules = resolve_module_dependencies(&all_module_paths)?;
        Ok(resolved_modules[main_module_index].clone())
    }
}

#[derive(Parser, Debug)]
struct ActionCompileModule {
    /// Options to pass to the compiler
    #[command(flatten)]
    compiler_options: CommandLineCompilerOptions,
    /// Specification for the module to compile
    #[command(flatten)]
    module_compile_options: CommandLineModuleCompileOptions,
    /// Output to write the compiled module to. If not provided, the file created will be {module_name}.gso
    #[arg(long, short)]
    output: Option<PathBuf>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
enum TypeTreeOutputFormat {
    Simple,
    Full,
}

#[derive(Debug, Parser)]
struct ActionEvalExpression {
    /// VM options to pass to the VM
    #[command(flatten)]
    vm_options: CommandLineVMOptions,
    /// Options to pass to the compiler
    #[command(flatten)]
    compiler_options: CommandLineCompilerOptions,
    /// Specification for the module to compile
    #[command(flatten)]
    module_compile_options: CommandLineModuleCompileOptions,
    /// Expression to eval against the input
    #[arg(long, short)]
    expression: String,
    /// Type of the value yielded by the expression. If not specified, default expression type is Typename
    #[arg(long, short = 'x')]
    expression_type: Option<String>,
    /// Output format for the type tree (if result is a type tree)
    #[arg(long, short = 'f')]
    output_format: Option<TypeTreeOutputFormat>,
}

#[derive(Debug, Parser)]
enum Action {
    /// Assembles low level gospel assembly source files to a module container
    Assemble(ActionAssembleModule),
    /// Call a named function with the provided arguments
    Call(ActionCallFunction),
    /// Disassembles the provided module container file
    Disassemble(ActionDisassembleModule),
    /// Parses the source file to an AST and dumps it to the standard output as JSON
    Parse(ActionParseSourceFile),
    /// Compiles module files into a module container
    Compile(ActionCompileModule),
    /// Compiles input files and evals an expression against them, and returns the result
    Eval(ActionEvalExpression),
}

#[derive(Debug, Parser)]
#[clap(version)]
struct TopLevelArgs {
    #[command(subcommand)]
    action: Action,
}

fn do_action_assemble(action: ActionAssembleModule) -> anyhow::Result<()> {
    let writer = Rc::new(RefCell::new(GospelContainerWriter::create(action.module_name.as_str())));
    let mut assembler = GospelAssembler::create(writer.clone());
    for source_file_name in &action.files {
        let file_contents = read_to_string(source_file_name)
            .map_err(|x| anyhow!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), x.to_string()))?;
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));
        assembler.assemble_file_contents(file_name.as_str(), file_contents.as_str())?;
    }

    let result_container = writer.borrow_mut().build()
        .map_err(|x| anyhow!("Failed to build container: {}", x.to_string()))?;
    let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gso", action.module_name)));
    if let Some(parent_directory) = output_file_name.parent() {
        create_dir_all(parent_directory).map_err(|x| anyhow!("Failed to create parent directories for file {}: {}", output_file_name.display(), x))?;
    }
    let container_serialized_data = result_container.write()
        .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
    write(output_file_name.clone(), container_serialized_data)
        .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;
    Ok({})
}

fn print_full_type_tree(type_tree: &TypeTree, root_type_container: Option<&GospelVMTypeContainer>, target_triplet: Option<TargetTriplet>) -> anyhow::Result<()> {
    let mut optional_type_layout_cache = target_triplet.map(|x| TypeLayoutCache::create(x));
    for type_index in 0..type_tree.types.len() {
        if type_index == type_tree.root_type_index {
            print!("[TREE ROOT] ");
        }
        if let Some(type_layout_cache) = optional_type_layout_cache.as_mut() {
            let type_data = type_tree.type_by_index(type_index);
            if !type_data.is_sizeless(type_tree) {
                match type_data.size_and_alignment(type_tree, type_layout_cache) {
                    Ok((size, alignment)) => {
                        println!("Type #{} (alignment: 0x{:x}; size: 0x{:x}): ", type_index, alignment, size);       
                    }
                    Err(layout_error) => {
                        println!("Type #{} (size calculation error: {}): ", type_index, layout_error);
                    }
                }
            } else {
                println!("Type #{} (sizeless): ", type_index);
            }
        } else {
            println!("Type #{}: ", type_index);
        }
        serde_json::to_string_pretty(type_tree.type_by_index(type_index))?.lines().for_each(|x| {
            println!(" | {}", x);
        });
        // TODO: Type indices printed as a part of type prototype are actually incorrect because they refer to the original type graph and not a sub-tree we have forked off
        if type_index == type_tree.root_type_index && let Some(root_type_container) = root_type_container {
            if let Some(member_prototypes) = &root_type_container.member_prototypes {
                println!(" |$ Type Prototype: ");
                serde_json::to_string_pretty(member_prototypes)?.lines().for_each(|x| {
                    println!(" |$ {}", x);
                });
            }
        }
        if let Some(type_layout_cache) = optional_type_layout_cache.as_mut() {
            if let Type::UDT(user_defined_type) = &type_tree.type_by_index(type_index) {
                println!(" |# UDT Layout:");
                match user_defined_type.layout(type_tree, type_layout_cache) {
                    Ok(type_layout) => {
                        serde_json::to_string_pretty(&type_layout.deref())?.lines().for_each(|x| {
                            println!(" |# {}", x);
                        });
                    }
                    Err(layout_error) => {
                        println!(" # <layout calculation error: {}>", layout_error);
                    }
                }
            } else if let Type::Enum(enum_type) = &type_tree.type_by_index(type_index) {
                match enum_type.underlying_type(&type_layout_cache.target_triplet) {
                    Ok(underlying_type) => {
                        println!(" |# Enum Underlying Type: {}", serde_json::to_string_pretty(&underlying_type)?);
                    }
                    Err(calculation_error) => {
                        println!(" # Enum Underlying Type: <underlying type calculation error: {}>", calculation_error);
                    }
                }
            }
        } else if let Type::Enum(enum_type) = &type_tree.type_by_index(type_index) &&
            let Some(static_underlying_type) = enum_type.underlying_type_no_target_no_constants() {
            println!(" |# Enum Underlying Type: {}", serde_json::to_string_pretty(&static_underlying_type)?);
        }
    }
    Ok({})
}

fn print_simplified_type_tree(type_tree: &TypeTree, target_triplet: Option<TargetTriplet>) -> anyhow::Result<()> {
    let mut type_layout_cache = TypeLayoutCache::create(target_triplet.ok_or_else(|| anyhow!("Simplified type tree format requires target triplet"))?);
    for type_in_tree in &type_tree.types {
        if let Type::UDT(user_defined_type) = type_in_tree {
            let layout = user_defined_type.layout(type_tree, &mut type_layout_cache)?;
            println!("{}.layout {{ // 0x{:x}", user_defined_type.name.as_deref().unwrap_or("<unknown>"), layout.size);
            for (member, member_layout) in user_defined_type.members.iter().zip(&layout.member_layouts) {
                match member_layout {
                    ResolvedUDTMemberLayout::Field(field) => {
                        println!("    0x{:x} {}", field.offset, member.name().unwrap_or("<unknown>"));
                    },
                    ResolvedUDTMemberLayout::Bitfield(field) => {
                        println!("    0x{:x} {} : {}", field.offset, member.name().unwrap_or("<unknown>"), field.bitfield_width);
                    }
                    ResolvedUDTMemberLayout::VirtualFunction(virtual_function) => {
                        println!("    vtable 0x{:x} offset 0x{:x} {}", virtual_function.vtable_offset, virtual_function.offset, member.name().unwrap_or("<unknown>"));
                    }
                }
            }
            println!("}}");
        }
    }
    Ok({})
}

fn print_type_tree(type_tree: &TypeTree, root_type_container: Option<&GospelVMTypeContainer>, target_triplet: Option<TargetTriplet>, print_format: TypeTreeOutputFormat) -> anyhow::Result<()> {
    if print_format == TypeTreeOutputFormat::Simple {
        print_simplified_type_tree(type_tree, target_triplet)
    } else {
        print_full_type_tree(type_tree, root_type_container, target_triplet)
    }
}

fn pretty_print_vm_value(value: &GospelVMValue, execution_context: &GospelVMRunContext, output_format: Option<TypeTreeOutputFormat>) -> anyhow::Result<()> {
    if let GospelVMValue::TypeReference(type_index) = value {
        let type_container = execution_context.type_container_by_index(*type_index);
        let type_tree = execution_context.type_tree(*type_index);
        let result_output_format = output_format.unwrap_or(TypeTreeOutputFormat::Full);
        print_type_tree(&type_tree, Some(type_container), execution_context.target_triplet().cloned(), result_output_format)?;
    } else {
        println!("Value: {}", serde_json::to_string_pretty(&value)?);
    };
    Ok({})
}

fn do_action_call(action: ActionCallFunction) -> anyhow::Result<()> {
    // Parse target triplet

    // Load containers to the VM
    let mut vm_state = GospelVMState::create();
    let mut all_containers: Vec<Rc<GospelVMContainer>> = Vec::new();

    for container_file_name in &action.input {
        let file_buffer = read(container_file_name)
            .map_err(|x| anyhow!("Failed to open container file {}: {}", container_file_name.to_string_lossy(), x.to_string()))?;
        let parsed_container = GospelContainer::read(&file_buffer)
            .map_err(|x| anyhow!("Failed to parse container file {}: {}", container_file_name.to_string_lossy(), x.to_string()))?;
        let mounted_container = vm_state.mount_container(parsed_container)
            .map_err(|x| anyhow!("Failed to mount container file {}: {}", container_file_name.to_string_lossy(), x.to_string()))?;
        all_containers.push(mounted_container);
    }

    // Find the function definition by name
    let result_function_pointer = if let Some(container_name) = &action.container_name {
        vm_state.find_named_container(container_name.as_str())
            .and_then(|x| x.find_named_function(action.function_name.as_str()))
            .ok_or_else(|| anyhow!("Failed to find a function named {} in container {}", action.container_name.as_ref().unwrap().clone(), action.function_name.clone()))?
    } else {
        all_containers.iter()
            .find_map(|x| x.find_named_function(action.function_name.as_str()))
            .ok_or_else(|| anyhow!("Failed to find a function named {} in any container", action.function_name.clone()))?
    };

    // Assemble and evaluate function arguments
    let mut function_arguments: Vec<GospelVMValue> = Vec::new();
    for argument_string in &action.function_args {
        let parsed_value = u64::from_str(argument_string)
            .map_err(|x| anyhow!("Failed to parse argument value as primitive \"{}\": {}", argument_string.clone(), x.to_string()))?;
        function_arguments.push(GospelVMValue::Primitive(parsed_value));
    }

    // Evaluate the function
    let mut execution_context = action.vm_options.create_run_context()?;
    let function_result = result_function_pointer.execute(function_arguments, &mut execution_context)
        .map_err(|x| anyhow!("Failed to execute function: {}", x.to_string()))?;

    // Print the result now
    pretty_print_vm_value(&function_result, &execution_context, action.output_format)
}

fn do_action_disassemble(action: ActionDisassembleModule) -> anyhow::Result<()> {
    let file_buffer = read(action.input.clone())
        .map_err(|x| anyhow!("Failed to open container file {}: {}", action.input.to_string_lossy(), x.to_string()))?;

    // Parse the module interface based on the file type and create the reflector object
    let parsed_container = GospelContainer::read(&file_buffer)
        .map_err(|x| anyhow!("Failed to parse module container file: {}", x.to_string()))?;
    let container_reader = GospelContainerReader{container: parsed_container};
    
    let result_disassembly_string = if let Some(function_name) = action.function_name {
        let target_function = container_reader.container_function_by_name(&function_name)
            .map_err(|x| anyhow!("Failed to read function data: {}", x))?
            .ok_or_else(|| anyhow!("Function with name {} is not found in the container", &function_name))?;
        disassemble_function(&target_function)
    } else {
        container_reader.container_functions().map_err(|x| anyhow!("Failed to read function data: {}", x))?.iter()
            .map(|function_data| disassemble_function(function_data))
            .join("\n")
    };

    if let Some(output_file_path) = action.output {
        write(output_file_path, result_disassembly_string.as_bytes())?;
    } else {
        println!("{}", result_disassembly_string);
    }
    Ok({})
}

fn do_action_parse(action: ActionParseSourceFile) -> anyhow::Result<()> {
    let file_name = action.input.to_string_lossy().to_string();
    let file_contents = read_to_string(action.input.clone())
        .map_err(|x| anyhow!("Failed to read file {}: {}", action.input.to_string_lossy(), x.to_string()))?;

    let result_module = parse_source_file(file_name.as_str(), file_contents.as_str())?;
    let serialized_module = serde_json::to_string_pretty(&result_module)?;

    if let Some(output_file_path) = action.output {
        write(output_file_path, serialized_module.as_bytes())?;
    } else {
        println!("{}", serialized_module);
    }
    Ok({})
}

fn do_action_compile(action: ActionCompileModule) -> anyhow::Result<()> {
    let module_definition = action.module_compile_options.resolve_module_dependencies()?;
    let compiler_instance = action.compiler_options.create_compiler_instance()?;

    let output_file_name = action.output.unwrap_or_else(|| module_definition.default_build_product_path());
    if let Some(parent_directory) = output_file_name.parent() {
        create_dir_all(parent_directory).map_err(|x| anyhow!("Failed to create parent directories for file {}: {}", output_file_name.display(), x))?;
    }

    // Include module dependencies to the VM and compile only the current module
    let result_container = module_definition.include_dependencies_and_compile_module(&compiler_instance)?;
    let container_serialized_data = result_container.write()
        .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
    write(output_file_name.clone(), container_serialized_data)
        .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;
    Ok({})
}

fn do_action_eval(action: ActionEvalExpression) -> anyhow::Result<()> {
    let module_definition = action.module_compile_options.resolve_module_dependencies()?;
    let compiler_instance = action.compiler_options.create_compiler_instance()?;

    // Compile full module tree and mount it to the VM state
    let module_containers = module_definition.compile_module_tree(&compiler_instance)?;
    let mut vm_state = GospelVMState::create();
    for module_container in module_containers {
        vm_state.mount_container(module_container).map_err(|x| anyhow!("Failed to mount module container: {}", x))?;
    }

    // Compile the provided expression in a separate module
    let expression_value_type = if let Some(value_type_string) = &action.expression_type {
        ExpressionValueType::from_str(value_type_string).map_err(|x| anyhow!("Unknown expression value type: {}. Allowed expression value types are typename and int", x))?
    } else { ExpressionValueType::Typename };
    let parsed_expression = parse_expression("<stdin>", action.expression.as_str())
        .map_err(|x| anyhow!("Failed to parse expression: {}", x))?;

    let module_writer = compiler_instance.define_module("@stdin_repl").to_simple_result()?;
    let function_reference = module_writer.add_simple_function("@stdin_repl", expression_value_type, &parsed_expression).to_simple_result()
        .map_err(|x| anyhow!("Failed to compile expression: {}", x))?;
    let result_module = module_writer.compile().map_err(|x| anyhow!("Failed to compile module: {}", x))?;
    let mounted_container = vm_state.mount_container(result_module).map_err(|x| anyhow!("Failed to mount module container: {}", x))?;

    // Evaluate the function
    let compiled_expression = mounted_container.find_named_function(function_reference.local_name.as_str()).ok_or_else(|| anyhow!("Failed to find compiled expression function"))?;
    let mut execution_context = action.vm_options.create_run_context()?;
    let function_result = compiled_expression.execute(Vec::new(), &mut execution_context)
        .map_err(|x| anyhow!("Failed to eval expression: {}", x.to_string()))?;

    // Print the result now
    pretty_print_vm_value(&function_result, &execution_context, action.output_format)
}

fn main() {
    let args = TopLevelArgs::parse();
    let result = match args.action {
        Action::Assemble(assemble_action) => do_action_assemble(assemble_action),
        Action::Call(call_action) => do_action_call(call_action),
        Action::Disassemble(reflect_action) => do_action_disassemble(reflect_action),
        Action::Parse(parse_action) => do_action_parse(parse_action),
        Action::Compile(compile_action) => do_action_compile(compile_action),
        Action::Eval(eval_action) => do_action_eval(eval_action),
    };
    if let Err(error) = result {
        error.to_string().lines().for_each(|x| {
            eprintln!("error: {}", x);
        });
        exit(1);
    }
}
