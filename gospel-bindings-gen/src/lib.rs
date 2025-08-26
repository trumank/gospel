use std::collections::{HashMap, HashSet};
use std::fs::write;
use std::path::PathBuf;
use anyhow::anyhow;
use crate::code_generator::CodeGenerationContext;
use crate::module_processor::process_module_context;

mod code_generator;
mod module_processor;

#[derive(Debug, Clone)]
pub struct ModuleBindingsOptions {
    pub additional_dependencies: Vec<PathBuf>,
    pub additional_included_module_names: HashSet<String>,
    pub module_to_bindings_crate_lookup: HashMap<String, String>,
}
impl Default for ModuleBindingsOptions {
    fn default() -> Self {
        Self{additional_dependencies: Vec::new(), additional_included_module_names: HashSet::new(), module_to_bindings_crate_lookup: HashMap::new()}
    }
}

pub fn generate_module_bindings(main_module_path: &PathBuf, output_file_path: &PathBuf, options: ModuleBindingsOptions) -> anyhow::Result<()> {
    let module_context = process_module_context(main_module_path, &options.additional_dependencies, &options.additional_included_module_names, &options.module_to_bindings_crate_lookup)?;
    let codegen_context = CodeGenerationContext{module_context, bindings_mod_name: String::from("gospel_bindings")};
    let generated_file_contents = codegen_context.generate_bindings_file()?;
    write(output_file_path, generated_file_contents).map_err(|x| anyhow!("Failed to write output file {}: {}", output_file_path.display(), x))
}
