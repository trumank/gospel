use std::fs::{read_to_string, write};
use std::path::PathBuf;
use std::process::exit;
use clap::Parser;
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
enum Action {
    /// Assembles low level gospel assembly source files to a type container
    Assemble(ActionAssembleContainer),
}

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

fn do_action_assemble(action: ActionAssembleContainer) {
    let mut container_writer = GospelContainerWriter::create(action.container_name.as_str());
    let mut failed_to_compile_files = false;
    
    let mut assembler = GospelAssembler::create(&mut container_writer);
    for source_file_name in &action.files {
        let file_read_result = read_to_string(source_file_name);
        if file_read_result.is_err() {
            eprintln!("Failed to open source file {}: {}", source_file_name.to_string_lossy(), file_read_result.unwrap_err().to_string());
            failed_to_compile_files = true;
            continue;
        }
        let file_contents = file_read_result.unwrap();
        let file_name = source_file_name.file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or(String::from("<unknown>"));
        let assembler_result = assembler.assemble_file_contents(file_name.as_str(), file_contents.as_str());
        if assembler_result.is_err() {
            eprintln!("Failed to assemble source file {}: {}", source_file_name.to_string_lossy(), assembler_result.unwrap_err().to_string());
            failed_to_compile_files = true;
        }
    }
    
    if failed_to_compile_files {
        eprintln!("Not writing container because one or more source files failed to compile");
        exit(1);
    }
    let result_container = container_writer.build();
    let output_file_name = action.output.unwrap_or_else(|| PathBuf::from(format!("{}.gso", action.container_name)));
    let container_serialize_result = result_container.write();
    
    if container_serialize_result.is_err() {
        eprintln!("Failed to serialize container: {}", container_serialize_result.unwrap_err().to_string());
        exit(1);
    }
    let write_result = write(output_file_name.clone(), container_serialize_result.unwrap());
    if write_result.is_err() {
        eprintln!("Failed to write container file {}: {}", output_file_name.to_string_lossy(), write_result.unwrap_err().to_string());
        exit(1);
    }
}

fn main() {
    let args = Args::parse();
    match args.action {
        Action::Assemble(assemble_action) => do_action_assemble(assemble_action),
    };
}
