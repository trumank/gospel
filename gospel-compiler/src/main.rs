use std::cell::RefCell;
use std::fs::{read, read_to_string, write};
use std::path::PathBuf;
use std::process::exit;
use std::rc::Rc;
use anyhow::{anyhow, bail};
use clap::Parser;
use gospel_typelib::type_model::{TargetTriplet, TypeGraphLike};
use gospel_vm::module::{GospelContainer};
use gospel_vm::reflection::{GospelContainerReflector, GospelModuleReflector};
use gospel_vm::vm::{GospelVMContainer, GospelVMRunContext, GospelVMState, GospelVMValue};
use gospel_vm::writer::{GospelContainerBuilder, GospelContainerWriter};
use crate::assembler::GospelAssembler;
use crate::ast::ExpressionValueType;
use crate::backend::{CompilerInstance, CompilerModuleBuilder, CompilerResultTrait};
use crate::parser::{parse_expression, parse_source_file};

pub mod assembler;
pub mod ast;
pub mod parser;
mod lex_util;
pub mod backend;

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

#[derive(Parser, Debug)]
struct ActionCallFunction {
    /// Container files to load to the VM before evaluation of the expression
    #[arg(long, short)]
    input: Vec<PathBuf>,
    /// Target triple to use as a platform config. When not provided, current platform will be used instead (environment is assumed to be native to the platform)
    #[arg(long, short)]
    target: Option<String>,
    /// Name of the container to find the function in, if not provided all containers are searched in the same order they are passed on the command line
    #[arg(long, short)]
    container_name: Option<String>,
    /// Name of the function to call
    #[arg(index = 1)]
    function_name: String,
    /// Optional arguments to provide to the function
    #[arg(index = 2)]
    function_args: Vec<String>,
}

#[derive(Parser, Debug)]
struct ActionReflectModule {
    /// Module container or reference container to print the public interface of
    #[arg(index = 1)]
    input: PathBuf,
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

#[derive(Parser, Debug)]
struct ActionCompileModule {
    /// Name of the module to compile. If not provided, base name of the first file is used
    #[arg(long, short)]
    module_name: Option<String>,
    /// Output to write the compiled module to. If not provided, the file created will be {module_name}.gso
    #[arg(long, short)]
    output: Option<PathBuf>,
    /// Files to compile into the module
    #[arg(index = 1)]
    files: Vec<PathBuf>,
}

#[derive(Parser, Debug)]
struct ActionEvalExpression {
    /// Target triple to use as a platform config. When not provided, current platform will be used instead (environment is assumed to be native to the platform)
    #[arg(long, short)]
    target: Option<String>,
    /// Name of the module to compile as. If not provided, name of the first input file is used
    #[arg(long, short)]
    module_name: Option<String>,
    /// Files to compile into the module
    #[arg(long, short)]
    input: Vec<PathBuf>,
    /// Expression to eval against the input
    #[arg(long, short)]
    expression: String,
}

#[derive(Parser, Debug)]
enum Action {
    /// Assembles low level gospel assembly source files to a module container
    Assemble(ActionAssembleModule),
    /// Call a named function with the provided arguments
    Call(ActionCallFunction),
    /// Prints information about the public interface of the given module. Note that this will not print any private module definitions or data
    Reflect(ActionReflectModule),
    /// Parses the source file to an AST and dumps it to the standard output as JSON
    Parse(ActionParseSourceFile),
    /// Compiles module files into a module container
    Compile(ActionCompileModule),
    /// Compiles input files and evals an expression against them, and returns the result
    Eval(ActionEvalExpression),
}

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
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
    let container_serialized_data = result_container.write()
        .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
    write(output_file_name.clone(), container_serialized_data)
        .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;
    Ok({})
}

fn do_action_call(action: ActionCallFunction) -> anyhow::Result<()> {
    // Parse target triplet
    let target_triplet = if let Some(target_triplet_name) = &action.target {
        TargetTriplet::parse(target_triplet_name.as_str())
            .map_err(|x| anyhow!("Failed to parse provided target triplet: {}", x.to_string()))?
    } else {
        TargetTriplet::current_target()
            .ok_or_else(|| anyhow!("Current platform is not a valid target. Please specify target manually with --target "))?
    };

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
        let assembled_value = GospelAssembler::assemble_static_value("<repl>", argument_string.as_str(), None)
            .map_err(|x| anyhow!("Failed to assemble argument value \"{}\": {}", argument_string.clone(), x.to_string()))?;
        let evaluated_value = vm_state.eval_source_value(&target_triplet, &assembled_value)
            .map_err(|x| anyhow!("Failed to eval argument value \"{}\": {}", argument_string.clone(), x.to_string()))?;
        function_arguments.push(evaluated_value);
    }

    // Evaluate the function
    let mut execution_context = GospelVMRunContext::create(&target_triplet);
    let function_result = result_function_pointer.execute(function_arguments, &mut execution_context)
        .map_err(|x| anyhow!("Failed to execute function: {}", x.to_string()))?;

    // Print the result now
    let serialized_result = if let GospelVMValue::TypeReference(type_index) = function_result {
        serde_json::to_string_pretty(&execution_context.type_tree(type_index))?
    } else { serde_json::to_string_pretty(&function_result)? };
    println!("{}", serialized_result);
    Ok({})
}

fn do_action_reflect(action: ActionReflectModule) -> anyhow::Result<()> {
    let file_buffer = read(action.input.clone())
        .map_err(|x| anyhow!("Failed to open container file {}: {}", action.input.to_string_lossy(), x.to_string()))?;

    // Parse the module interface based on the file type and create the reflector object
    let parsed_container = GospelContainer::read(&file_buffer)
        .map_err(|x| anyhow!("Failed to parse module container file: {}", x.to_string()))?;
    let module_reflector = GospelContainerReflector::create(Rc::new(parsed_container))
        .map_err(|x| anyhow!("Failed to reflect module container file: {}", x.to_string()))?;

    // Print the resulting data now
    println!("Module {} public interface:", module_reflector.module_name()?);
    for global_variable in module_reflector.enumerate_globals()? {
        println!(" extern global {};", global_variable.name);
    }
    for function_info in module_reflector.enumerate_functions()? {
        let arguments: Vec<String> = function_info.arguments.iter().enumerate().map(|(index, argument)| {
            format!("${}: {}", index, argument.argument_type)
        }).collect();
        let function_declaration = if arguments.is_empty() {
            format!("{} -> {}", function_info.name, function_info.return_value_type)
        } else {
            format!("{} {} -> {}", function_info.name, arguments.join(" "), function_info.return_value_type)
        };
        println!(" function {};", function_declaration);
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
    if action.files.is_empty() {
       bail!("No source files provided");
    }
    let first_file_base_name = action.files[0].file_stem().map(|x| x.to_string_lossy().to_string())
        .ok_or_else(|| anyhow!("First source file name provided is not a valid file name"))?;
    let module_name = action.module_name.unwrap_or(first_file_base_name);

    let compiler_instance = CompilerInstance::create();
    let module_writer = compiler_instance.define_module(&module_name).to_simple_result()?;

    for source_file_name in &action.files {
        let file_contents = read_to_string(source_file_name)
            .map_err(|x| anyhow!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), x.to_string()))?;
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));

        let module_source_file = parse_source_file(file_name.as_str(), file_contents.as_str())
            .map_err(|x| anyhow!("Failed to parse source file {}: {}", file_name, x))?;
        module_writer.add_source_file(module_source_file).to_simple_result()
            .map_err(|x| anyhow!("Failed to pre-compile source file {}: {}", file_name, x))?;
    }
    let result_container = module_writer.compile().to_simple_result()
        .map_err(|x| anyhow!("Failed to compile module: {}", x.to_string()))?;
    let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gso", module_name.as_str())));
    let container_serialized_data = result_container.write()
        .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
    write(output_file_name.clone(), container_serialized_data)
        .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;
    Ok({})
}

fn do_action_eval(action: ActionEvalExpression) -> anyhow::Result<()> {
    // Parse target triplet
    let target_triplet = if let Some(target_triplet_name) = &action.target {
        TargetTriplet::parse(target_triplet_name.as_str())
            .map_err(|x| anyhow!("Failed to parse provided target triplet: {}", x.to_string()))?
    } else {
        TargetTriplet::current_target()
            .ok_or_else(|| anyhow!("Current platform is not a valid target. Please specify target manually with --target "))?
    };
    if action.input.is_empty() {
        bail!("No source files provided");
    }
    let first_file_base_name = action.input[0].file_stem().map(|x| x.to_string_lossy().to_string())
        .ok_or_else(|| anyhow!("First source file name provided is not a valid file name"))?;
    let module_name = action.module_name.unwrap_or(first_file_base_name);

    let compiler_instance = CompilerInstance::create();
    let module_writer = compiler_instance.define_module(&module_name).to_simple_result()?;

    // Compile provided source files first
    for source_file_name in &action.input {
        let file_contents = read_to_string(source_file_name)
            .map_err(|x| anyhow!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), x.to_string()))?;
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));

        let module_source_file = parse_source_file(file_name.as_str(), file_contents.as_str())
            .map_err(|x| anyhow!("Failed to parse source file {}: {}", file_name, x))?;
        module_writer.add_source_file(module_source_file).to_simple_result()
            .map_err(|x| anyhow!("Failed to compile source file {}: {}", file_name, x))?;
    }
    // Compile the provided expression into a generated function
    let parsed_expression = parse_expression("<stdin>", action.expression.as_str())
        .map_err(|x| anyhow!("Failed to parse expression: {}", x))?;
    let function_reference = module_writer.add_simple_function("@stdin_repl", ExpressionValueType::Typename, &parsed_expression).to_simple_result()
        .map_err(|x| anyhow!("Failed to compile expression: {}", x))?;

    let mut vm_state = GospelVMState::create();
    let mounted_container = vm_state.mount_container(module_writer.compile().to_simple_result()
        .map_err(|x| anyhow!("Failed to compile module: {}", x))?)?;
    let compiled_expression = mounted_container.find_named_function(function_reference.local_name.as_str()).ok_or_else(|| anyhow!("Failed to find compiled expression function"))?;

    // Evaluate the function
    let mut execution_context = GospelVMRunContext::create(&target_triplet);
    let function_result = compiled_expression.execute(Vec::new(), &mut execution_context)
        .map_err(|x| anyhow!("Failed to eval expression: {}", x.to_string()))?;
    // Print the result now
    let serialized_result = if let GospelVMValue::TypeReference(type_index) = function_result {
        serde_json::to_string_pretty(&execution_context.type_tree(type_index))?
    } else { serde_json::to_string_pretty(&function_result)? };
    println!("{}", serialized_result);
    Ok({})
}

fn main() {
    let args = Args::parse();
    let result = match args.action {
        Action::Assemble(assemble_action) => do_action_assemble(assemble_action),
        Action::Call(call_action) => do_action_call(call_action),
        Action::Reflect(reflect_action) => do_action_reflect(reflect_action),
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
