use std::cell::RefCell;
use std::fs::{read, read_to_string, write};
use std::path::PathBuf;
use std::process::exit;
use std::rc::Rc;
use anyhow::{anyhow};
use clap::Parser;
use gospel_vm::container::{GospelCommonFileHeader, GospelCommonFileType, GospelContainer, GospelRefContainer};
use gospel_vm::reflection::GospelModuleReflectable;
use gospel_vm::vm::{GospelVMContainer, GospelVMState, GospelVMTargetTriplet, GospelVMValue};
use gospel_vm::writer::{GospelBuildFromModuleSource, GospelModuleBuilder, GospelModuleVisitor, GospelMultiContainerVisitor};
use crate::assembler::GospelAssembler;

pub mod assembler;

#[derive(Parser, Debug)]
struct ActionAssembleModule {
    /// Name of the resulting module
    #[arg(index = 1)]
    module_name: String,
    /// Name of the container output file to write. Default is container_name.gso
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// When provided, produce a reference container with public module definitions instead of a full module container
    /// Assembly files are allowed to have function declarations in this mode, otherwise only function definitions are allowed
    #[arg(long)]
    interface: bool,
    /// Normally, assemble will produce a module container as well as a sidecar file with public definitions for the assembled module
    /// When this option is given, no public definitions container is produced.
    #[arg(long)]
    no_ref_container: bool,
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
struct ActionReflectModule {
    /// Module container or reference container to print the public interface of
    #[arg(index = 1)]
    input: PathBuf,
}

#[derive(Parser, Debug)]
enum Action {
    /// Assembles low level gospel assembly source files to a module container
    Assemble(ActionAssembleModule),
    /// Eval a named function with the provided arguments
    Eval(ActionEvalFunction),
    /// Prints information about the public interface of the given module. Note that this will not print any private module definitions or data
    Reflect(ActionReflectModule),
}

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

fn do_action_assemble(action: ActionAssembleModule) -> anyhow::Result<()> {
    let composite_writer = RefCell::new(GospelMultiContainerVisitor::default());

    // Add writers for the main module definition container and the public interface container
    let mut container_writer: Option<Rc<RefCell<dyn GospelModuleBuilder<GospelContainer>>>> = None;
    let mut reference_container_writer: Option<Rc<RefCell<dyn GospelModuleBuilder<GospelRefContainer>>>> = None;
    if !action.interface {
        container_writer = Some(GospelContainer::make_builder(action.module_name.as_str()));
        let container_module_visitor = container_writer.as_ref().unwrap().clone() as Rc<RefCell<dyn GospelModuleVisitor>>;
        composite_writer.borrow_mut().add_visitor(container_module_visitor);
    }
    if action.interface || !action.no_ref_container {
        reference_container_writer = Some(GospelRefContainer::make_builder(action.module_name.as_str()));
        let ref_container_module_visitor = reference_container_writer.as_ref().unwrap().clone() as Rc<RefCell<dyn GospelModuleVisitor>>;
        composite_writer.borrow_mut().add_visitor(ref_container_module_visitor);
    }

    let mut assembler = GospelAssembler::create(Rc::new(composite_writer));
    for source_file_name in &action.files {
        let file_contents = read_to_string(source_file_name)
            .map_err(|x| anyhow!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), x.to_string()))?;
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));
        assembler.assemble_file_contents(file_name.as_str(), file_contents.as_str())?;
    }

    if !action.interface {
        let result_container = container_writer.unwrap().borrow_mut().build();
        let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gso", action.module_name)));
        let container_serialized_data = result_container.write()
            .map_err(|x| anyhow!("Failed to serialize container: {}", x.to_string()))?;
        write(output_file_name.clone(), container_serialized_data)
            .map_err(|x| anyhow!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;

        if !action.no_ref_container {
            let result_ref_container = reference_container_writer.unwrap().borrow_mut().build();
            let ref_output_file_name = output_file_name.with_extension("gsr");
            let ref_container_serialized_data = result_ref_container.write()
                .map_err(|x| anyhow!("Failed to serialize reference container: {}", x.to_string()))?;
            write(ref_output_file_name.clone(), ref_container_serialized_data)
                .map_err(|x| anyhow!("Failed to write reference container file {}: {}", ref_output_file_name.to_string_lossy(), x.to_string()))?;
        }
    } else {
        let result_container = reference_container_writer.unwrap().borrow_mut().build();
        let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gsr", action.module_name)));
        let container_serialized_data = result_container.write()
            .map_err(|x| anyhow!("Failed to serialize interface container: {}", x.to_string()))?;
        write(output_file_name.clone(), container_serialized_data)
            .map_err(|x| anyhow!("Failed to write interface container file {}: {}", output_file_name.to_string_lossy(), x.to_string()))?;
    }
    Ok({})
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

fn do_action_reflect(action: ActionReflectModule) -> anyhow::Result<()> {
    let file_buffer = read(action.input.clone())
        .map_err(|x| anyhow!("Failed to open container file {}: {}", action.input.to_string_lossy(), x.to_string()))?;

    // Read the common header to determine the type of file we are dealing with
    let common_file_header = GospelCommonFileHeader::try_read_file_header(&file_buffer)
        .map_err(|x| anyhow!("Failed to read common module header: {}", x.to_string()))?;

    // Parse the module interface based on the file type and create the reflector object
    let module_reflector = match common_file_header.file_type {
        GospelCommonFileType::Container => {
            let parsed_container = GospelContainer::read(&file_buffer)
                .map_err(|x| anyhow!("Failed to parse module container file: {}", x.to_string()))?;
            Rc::new(parsed_container).reflect()
                .map_err(|x| anyhow!("Failed to reflect module container file: {}", x.to_string()))?
        }
        GospelCommonFileType::RefContainer => {
            let parsed_ref_container = GospelRefContainer::read(&file_buffer)
                .map_err(|x| anyhow!("Failed to parse module reference container file: {}", x.to_string()))?;
            Rc::new(parsed_ref_container).reflect()
                .map_err(|x| anyhow!("Failed to reflect module reference container file: {}", x.to_string()))?
        }
    };

    // Print the resulting data now
    println!("Module {} public interface (from {}):", module_reflector.module_name()?, common_file_header.file_type);
    for global_variable in module_reflector.enumerate_globals()? {
        println!(" extern global {};", global_variable.name);
    }
    for function_info in module_reflector.enumerate_functions()? {
        let arguments: Vec<String> = function_info.arguments.iter().enumerate().map(|(index, argument)| {
            if argument.has_default_value {
                format!("${}: {} = $default", index, argument.argument_type)
            } else {
                format!("${}: {}", index, argument.argument_type)
            }
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

fn main() {
    let args = Args::parse();
    let result = match args.action {
        Action::Assemble(assemble_action) => do_action_assemble(assemble_action),
        Action::Eval(eval_action) => do_action_eval(eval_action),
        Action::Reflect(reflect_action) => do_action_reflect(reflect_action),
    };
    if let Err(error) = result {
        eprintln!("error: {}", error.to_string());
        exit(1);
    }
}
