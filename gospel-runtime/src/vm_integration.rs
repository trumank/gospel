use std::path::PathBuf;
use std::str::FromStr;
use anyhow::anyhow;
use gospel_typelib::type_model::{MutableTypeGraph, Type, TypeGraphLike};
use gospel_vm::vm::{GospelVMOptions, GospelVMRunContext, GospelVMState, GospelVMValue};
use gospel_vm::writer::GospelSourceObjectReference;
#[cfg(feature = "compiler")]
use gospel_compiler::backend::{CompilerInstance, CompilerOptions};
#[cfg(feature = "compiler")]
use gospel_compiler::module_definition::resolve_module_dependencies;

#[derive(Debug)]
pub struct GospelVMTypeGraphBackend {
    pub vm_instance: GospelVMState,
    pub vm_run_context: GospelVMRunContext,
}
impl GospelVMTypeGraphBackend {
    #[cfg(feature = "compiler")]
    pub fn create_from_module_tree(module_path: &PathBuf, additional_dependencies: &Vec<PathBuf>, vm_options: GospelVMOptions) -> anyhow::Result<GospelVMTypeGraphBackend> {
        let mut root_module_paths: Vec<PathBuf> = Vec::new();
        root_module_paths.push(module_path.clone());
        root_module_paths.extend(additional_dependencies.iter().cloned());

        let resolved_root_modules = resolve_module_dependencies(&root_module_paths)?;
        let main_module_path = resolved_root_modules[0].clone();

        let compiler_instance = CompilerInstance::create(CompilerOptions::default());
        let compiled_module_tree = main_module_path.compile_module_tree(&compiler_instance)?;

        let mut vm_instance = GospelVMState::create();
        for module_container in compiled_module_tree {
            vm_instance.mount_container(module_container)?;
        }
        let vm_run_context = GospelVMRunContext::create(vm_options);
        Ok(GospelVMTypeGraphBackend{vm_instance, vm_run_context})
    }
}

impl TypeGraphLike for GospelVMTypeGraphBackend {
    fn type_by_index(&self, type_index: usize) -> &Type {
        self.vm_run_context.type_by_index(type_index)
    }
}
impl MutableTypeGraph for GospelVMTypeGraphBackend {
    fn store_type(&mut self, type_data: Type) -> usize {
        self.vm_run_context.store_type(type_data)
    }
    fn find_create_named_udt_type(&mut self, full_type_name: &str) -> anyhow::Result<Option<usize>> {
        let object_reference = GospelSourceObjectReference::from_str(full_type_name)
            .map_err(|x| anyhow!("Malformed typename {} format: {}", full_type_name, x))?;
        if let Some(found_function_instance) = self.vm_instance.find_function_by_reference(&object_reference) {
            let function_result = found_function_instance.execute(Vec::new(), &mut self.vm_run_context)
                .map_err(|x| anyhow!("Failed to calculate layout for type {}: {}", full_type_name, x))?;
            if let GospelVMValue::TypeReference(type_index) = function_result {
                Ok(Some(type_index))
            } else { Err(anyhow!("Name {} does not refer to a type", full_type_name)) }
        } else { Ok(None) }
    }
}
