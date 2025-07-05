use std::fs::{read, read_to_string, write};
use std::path::PathBuf;
use std::process::exit;
use std::rc::Rc;
use anyhow::{anyhow};
use clap::Parser;
use gospel_vm::container::GospelContainer;
use gospel_vm::vm::{GospelVMContainer, GospelVMState, GospelVMTargetTriplet, GospelVMValue};
use gospel_vm::writer::GospelContainerWriter;
use crate::assembler::GospelAssembler;

pub mod assembler;

#[derive(Parser, Debug)]
struct ActionAssembleContainer {
    /// Name of the resulting type container
    #[arg(index = 1)]
    container_name: String,
    /// Name of the container output file to write. Default is container_name.gso
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Assembly files to compile to the container
    #[arg(index = 2)]
    files: Vec<PathBuf>,
}

#[derive(Parser, Debug)]
struct ActionEvalFunction {
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
enum Action {
    /// Assembles low level gospel assembly source files to a type container
    Assemble(ActionAssembleContainer),
    /// Eval a named function with the provided arguments
    Eval(ActionEvalFunction),
}

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

fn do_action_assemble(action: ActionAssembleContainer) -> anyhow::Result<()> {
    let mut container_writer = GospelContainerWriter::create(action.container_name.as_str());
    
    let mut assembler = GospelAssembler::create(&mut container_writer);
    for source_file_name in &action.files {
        let file_contents = read_to_string(source_file_name)
            .map_err(|x| anyhow!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), x.to_string()))?;
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));
        assembler.assemble_file_contents(file_name.as_str(), file_contents.as_str())?;
    }

    let result_container = container_writer.build();
    let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gso", action.container_name)));
    let container_serialized_data = result_container.write()
        .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
    write(output_file_name.clone(), container_serialized_data)
        .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))
}

fn do_action_eval(action: ActionEvalFunction) -> anyhow::Result<()> {
    // Parse target triplet
    let target_triplet = if let Some(target_triplet_name) = &action.target {
        GospelVMTargetTriplet::parse(target_triplet_name.as_str())
            .map_err(|x| anyhow!("Failed to parse provided target triplet: {}", x.to_string()))?
    } else {
        GospelVMTargetTriplet::current_target()
            .ok_or_else(|| anyhow!("Current platform is not a valid target. Please specify target manually with --target "))?
    };

    // Load containers to the VM
    let mut vm_state = GospelVMState::create(target_triplet);
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
            .map(|x| x.find_named_function(action.function_name.as_str()))
            .find(|x| x.is_some()).flatten()
            .ok_or_else(|| anyhow!("Failed to find a function named {} in any container", action.function_name.clone()))?
    };

    // Assemble and evaluate function arguments
    let mut function_arguments: Vec<GospelVMValue> = Vec::new();
    for argument_string in &action.function_args {
        let assembled_value = GospelAssembler::assemble_static_value("<repl>", argument_string.as_str())
            .map_err(|x| anyhow!("Failed to assemble argument value \"{}\": {}", argument_string.clone(), x.to_string()))?;
        let evaluated_value = vm_state.eval_source_value(&assembled_value, &Some(result_function_pointer.source_container()))
            .map_err(|x| anyhow!("Failed to eval argument value \"{}\": {}", argument_string.clone(), x.to_string()))?;
        function_arguments.push(evaluated_value);
    }

    // Evaluate the function
    let function_result = result_function_pointer.execute(&function_arguments)
        .map_err(|x| anyhow!("Failed to execute function: {}", x.to_string()))?;
    // Print the result now
    println!("{}", function_result);
    // Added because RustRover does not let you scroll to the end of a really long line newline at the end
    println!();
    Ok({})
}

fn main() {
    let args = Args::parse();
    let result = match args.action {
        Action::Assemble(assemble_action) => do_action_assemble(assemble_action),
        Action::Eval(eval_action) => do_action_eval(eval_action),
    };
    if let Err(error) = result {
        eprintln!("error: {}", error.to_string());
        exit(1);
    }
}
