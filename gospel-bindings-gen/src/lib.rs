use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::write;
use std::path::PathBuf;
use std::process::exit;
use anyhow::anyhow;
use gospel_typelib::target_triplet::TargetTriplet;
use gospel_vm::vm::GospelVMOptions;
use crate::code_generator::CodeGenerationContext;
use crate::module_processor::process_module_context;

mod code_generator;
mod module_processor;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ModuleBindingsType {
    Local,
    External,
}

#[derive(Debug, Clone)]
pub struct ModuleBindingsOptions {
    pub bindings_type: ModuleBindingsType,
    pub target_triplet: Option<TargetTriplet>,
    pub additional_dependencies: Vec<PathBuf>,
    pub additional_included_module_names: HashSet<String>,
    pub module_to_bindings_crate_lookup: HashMap<String, String>,
    pub type_universe_full_name: String,
}
impl Default for ModuleBindingsOptions {
    fn default() -> Self {
        Self{bindings_type: ModuleBindingsType::External, target_triplet: None, additional_dependencies: Vec::new(), additional_included_module_names: HashSet::new(),
            module_to_bindings_crate_lookup: HashMap::new(), type_universe_full_name: String::from("gospel_runtime::vm_integration::GospelVMTypeUniverse")}
    }
}

pub fn generate_module_bindings(main_module_path: &PathBuf, output_file_path: &PathBuf, options: ModuleBindingsOptions) -> anyhow::Result<()> {
    let mut vm_options = GospelVMOptions::default().no_default_globals();
    if options.bindings_type == ModuleBindingsType::Local {
        vm_options = vm_options.target_triplet(options.target_triplet.ok_or_else(|| anyhow!("Target triplet required for local bindings model"))?);
    }
    let module_context = process_module_context(main_module_path, &options.additional_dependencies, &options.additional_included_module_names, &options.module_to_bindings_crate_lookup, vm_options)?;

    let codegen_context = CodeGenerationContext{bindings_type: options.bindings_type, module_context, bindings_mod_name: String::from("gospel_bindings"),
        extra_definitions: RefCell::default(), generated_extra_types: RefCell::default(), type_universe_full_name: options.type_universe_full_name};
    let generated_file_contents = codegen_context.generate_bindings_file()?;
    write(output_file_path, generated_file_contents).map_err(|x| anyhow!("Failed to write output file {}: {}", output_file_path.display(), x))
}

pub fn build_rs_generate_bindings(module_name: &str, bindings_type: ModuleBindingsType) {
    let output_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let output_file_path = output_dir.join("gospel_bindings.rs");

    let mut bindings_options = ModuleBindingsOptions{bindings_type, ..ModuleBindingsOptions::default()};
    if bindings_options.bindings_type == ModuleBindingsType::Local {
        // We cannot use compiled_target_triplet here since we are running as a build script, and build scripts are built for the host compiler target, not for the compilation target
        let compiled_target_triplet = env::var("TARGET").unwrap();
        bindings_options.target_triplet = Some(TargetTriplet::parse(&compiled_target_triplet).unwrap_or_else(|| panic!("Unsupported target triplet for local type model")));
    }

    let current_package_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let module_dir = current_package_dir.join("res").join("gospel").join(module_name);
    println!("cargo::rerun-if-changed={}", module_dir.display());

    if let Err(generation_error) = generate_module_bindings(&module_dir, &output_file_path, bindings_options) {
        println!("cargo::error={}", generation_error);
        exit(1);
    }
}
