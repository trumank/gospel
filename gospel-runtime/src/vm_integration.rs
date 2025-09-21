use std::path::PathBuf;
use std::ptr::null_mut;
use std::str::FromStr;
use std::sync::{Mutex, RwLock};
use std::sync::atomic::{AtomicPtr, Ordering};
use anyhow::anyhow;
use gospel_typelib::type_model::{MutableTypeGraph, TargetTriplet, Type, TypeGraphLike, TypeTemplateArgument};
use gospel_vm::vm::{GospelVMOptions, GospelVMRunContext, GospelVMState, GospelVMValue};
use gospel_vm::writer::GospelSourceObjectReference;
#[cfg(feature = "compiler")]
use gospel_compiler::backend::{CompilerInstance, CompilerOptions};
#[cfg(feature = "compiler")]
use gospel_compiler::module_definition::resolve_module_dependencies;
use lazy_static::lazy_static;
use crate::core_type_definitions::StaticTypeLayoutCache;
use crate::external_type_model::TypeNamespace;
use crate::local_type_model::TypeUniverse;

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
    pub fn to_type_ptr_namespace(self) -> GospelVMTypeNamespace {
        let target_triplet = self.vm_run_context.target_triplet().unwrap().clone();
        let static_type_cache = Mutex::new(StaticTypeLayoutCache::create(target_triplet));
        GospelVMTypeNamespace{target_triplet, type_graph: RwLock::new(self), static_type_cache}
    }
}

pub struct GospelVMTypeNamespace {
    target_triplet: TargetTriplet,
    pub type_graph: RwLock<GospelVMTypeGraphBackend>,
    static_type_cache: Mutex<StaticTypeLayoutCache>,
}
impl TypeNamespace for GospelVMTypeNamespace {
    fn type_target_triplet(&self) -> TargetTriplet {
        self.target_triplet
    }
    fn type_graph(&self) -> &RwLock<dyn MutableTypeGraph> {
        &self.type_graph
    }
    fn type_layout_cache(&self) -> &Mutex<StaticTypeLayoutCache> {
        &self.static_type_cache
    }
}

pub enum GospelVMTypeUniverse {}
impl GospelVMTypeUniverse {
    /// Sets up type graph backend for the default Gospel VM type universe.
    /// Will panic if backend is set more than once
    /// This function is not thread safe, and you must ensure that there is no race condition with type_graph_backend
    pub fn set_type_graph_backend(backend: GospelVMTypeGraphBackend) {
        let type_graph_backend = Self::type_graph_backend_ref();
        if type_graph_backend.load(Ordering::Relaxed) != null_mut() {
            panic!("Attempt to set type graph on GospelVMTypeUniverse after it has already been set");
        }
        type_graph_backend.store(Box::into_raw(Box::new(Some(RwLock::new(backend)))), Ordering::Relaxed);
    }
    /// Returns the currently set type graph backend. Will panic if no type graph backend has been set
    pub fn type_graph_backend() -> &'static RwLock<GospelVMTypeGraphBackend> {
        let type_graph_backend = Self::type_graph_backend_ref().load(Ordering::Relaxed);
        if type_graph_backend == null_mut() {
            panic!("Attempt to access type graph on GospelVMTypeUniverse before it is set");
        }
        unsafe { type_graph_backend.as_ref_unchecked() }.as_ref().unwrap()
    }
    fn type_graph_backend_ref() -> &'static AtomicPtr<Option<RwLock<GospelVMTypeGraphBackend>>> {
        static STATIC_TYPE_GRAPH: AtomicPtr<Option<RwLock<GospelVMTypeGraphBackend>>> = AtomicPtr::new(null_mut());
        &STATIC_TYPE_GRAPH
    }
}
impl TypeUniverse for GospelVMTypeUniverse {
    fn target_triplet() -> TargetTriplet {
        lazy_static! {
            static ref cached_target_triplet: TargetTriplet = GospelVMTypeUniverse::type_graph_backend().read().unwrap().vm_run_context.target_triplet().cloned().unwrap();
        }
        *cached_target_triplet
    }
    fn type_graph() -> &'static RwLock<dyn MutableTypeGraph> {
        GospelVMTypeUniverse::type_graph_backend()
    }
    fn type_layout_cache() -> &'static Mutex<StaticTypeLayoutCache> {
        lazy_static! {
            static ref type_layout_cache: Mutex<StaticTypeLayoutCache> = Mutex::new(StaticTypeLayoutCache::create(GospelVMTypeUniverse::target_triplet()));
        }
        &*type_layout_cache
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
    fn create_named_type(&mut self, full_type_name: &str, arguments: Vec<TypeTemplateArgument>) -> anyhow::Result<Option<usize>> {
        let object_reference = GospelSourceObjectReference::from_str(full_type_name)
            .map_err(|x| anyhow!("Malformed typename {} format: {}", full_type_name, x))?;
        if let Some(found_function_instance) = self.vm_instance.find_function_by_reference(&object_reference) {
            let mapped_arguments: Vec<GospelVMValue> = arguments.into_iter().map(|x| match x {
                TypeTemplateArgument::Integer(integral_value) => GospelVMValue::Primitive(integral_value),
                TypeTemplateArgument::Type(type_index) => GospelVMValue::TypeReference(type_index),
            }).collect();
            let function_result = found_function_instance.execute(mapped_arguments, &mut self.vm_run_context)
                .map_err(|x| anyhow!("Failed to calculate layout for type {}: {}", full_type_name, x))?;
            if let GospelVMValue::TypeReference(type_index) = function_result {
                Ok(Some(type_index))
            } else { Err(anyhow!("Name {} does not refer to a type", full_type_name)) }
        } else { Ok(None) }
    }
}
