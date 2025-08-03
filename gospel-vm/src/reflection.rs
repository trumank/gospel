use std::collections::HashMap;
use std::rc::Rc;
use crate::container::{GospelContainer};
use crate::gospel_type::GospelValueType;

/// Reflected information about a global variable declared by a module
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelReflectedGlobalInfo {
    pub name: String,
}

/// Reflected information about a function argument
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelReflectedFunctionArgumentInfo {
    pub argument_type: GospelValueType,
}

/// Reflected information about a function defined by a module
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GospelReflectedFunctionInfo {
    pub name: String,
    pub return_value_type: GospelValueType,
    pub arguments: Vec<GospelReflectedFunctionArgumentInfo>,
}

/// Interface that allows introspection of gospel modules, such as listing their defines functions and globals
/// Module provides implementation of this trait for querying information from containers, reference containers, and VM containers
pub trait GospelModuleReflector {
    fn module_name(&self) -> anyhow::Result<String>;
    fn enumerate_globals(&self) -> anyhow::Result<Vec<GospelReflectedGlobalInfo>>;
    fn find_global(&self, name: &str) -> anyhow::Result<Option<GospelReflectedGlobalInfo>>;
    fn enumerate_functions(&self) -> anyhow::Result<Vec<GospelReflectedFunctionInfo>>;
    fn find_function(&self, name: &str) -> anyhow::Result<Option<GospelReflectedFunctionInfo>>;
    // TODO: Reflected info about structs defined in the container
}

/// Container reflector for Gospel Containers and reference containers
#[derive(Debug)]
pub struct GospelContainerReflector {
    container: Rc<GospelContainer>,
    global_name_lookup: HashMap<String, u32>,
    function_name_pair_name_lookup: HashMap<String, u32>,
}
impl GospelContainerReflector {
    /// Creates a new reflector instance from a container object
    pub fn create(container: Rc<GospelContainer>) -> anyhow::Result<Self> {
        // Build global variable name lookup
        let mut global_name_lookup: HashMap<String, u32> = HashMap::with_capacity(container.globals.len());
        for global_index in 0..container.globals.len() {
            let global_name_index = container.globals[global_index].name;
            let global_name = container.strings.get(global_name_index)?;
            global_name_lookup.insert(global_name.to_string(), global_index as u32);
        }

        // Build function name pair lookup
        let mut function_name_pair_name_lookup: HashMap<String, u32> = HashMap::with_capacity(container.function_names.len());
        for function_name_pair_index in 0..container.function_names.len() {
            let function_name = container.strings.get(container.function_names[function_name_pair_index].object_name)?;
            function_name_pair_name_lookup.insert(function_name.to_string(), function_name_pair_index as u32);
        }
        Ok(Self{container, global_name_lookup, function_name_pair_name_lookup})
    }
    fn make_global_info(&self, global_index: u32) -> anyhow::Result<GospelReflectedGlobalInfo> {
        let global_descriptor = &self.container.globals[global_index as usize];
        let name = self.container.strings.get(global_descriptor.name)?.to_string();
        Ok(GospelReflectedGlobalInfo{name})
    }
    fn make_function_info(&self, function_name_pair_index: u32) -> anyhow::Result<GospelReflectedFunctionInfo> {
        let name_pair = &self.container.function_names[function_name_pair_index as usize];
        let function_descriptor = &self.container.functions[name_pair.object_index as usize];
        let name = self.container.strings.get(name_pair.object_name)?.to_string();
        let return_value_type = function_descriptor.return_value_type;
        let arguments: Vec<GospelReflectedFunctionArgumentInfo> = function_descriptor.arguments.iter().map(|x| GospelReflectedFunctionArgumentInfo{
            argument_type: x.argument_type,
        }).collect();
        Ok(GospelReflectedFunctionInfo{name, return_value_type, arguments})
    }
}
impl GospelModuleReflector for GospelContainerReflector {
    fn module_name(&self) -> anyhow::Result<String> {
        self.container.container_name().map(|x| x.to_string())
    }
    fn enumerate_globals(&self) -> anyhow::Result<Vec<GospelReflectedGlobalInfo>> {
        let mut result: Vec<GospelReflectedGlobalInfo> = Vec::with_capacity(self.container.globals.len());
        for global_index in 0..self.container.globals.len() {
            result.push(self.make_global_info(global_index as u32)?);
        }
        Ok(result)
    }
    fn find_global(&self, name: &str) -> anyhow::Result<Option<GospelReflectedGlobalInfo>> {
        if let Some(global_index) = self.global_name_lookup.get(name) {
            Ok(Some(self.make_global_info(*global_index)?))
        } else { Ok(None) }
    }
    fn enumerate_functions(&self) -> anyhow::Result<Vec<GospelReflectedFunctionInfo>> {
        let mut result: Vec<GospelReflectedFunctionInfo> = Vec::with_capacity(self.container.function_names.len());
        for function_name_pair_index in 0..self.container.function_names.len() {
            result.push(self.make_function_info(function_name_pair_index as u32)?);
        }
        Ok(result)
    }
    fn find_function(&self, name: &str) -> anyhow::Result<Option<GospelReflectedFunctionInfo>> {
        if let Some(function_name_pair_index) = self.function_name_pair_name_lookup.get(name) {
            Ok(Some(self.make_function_info(*function_name_pair_index)?))
        } else { Ok(None) }
    }
}
