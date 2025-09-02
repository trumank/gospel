use anyhow::bail;
use crate::bytecode::GospelInstruction;
use crate::gospel::GospelObjectIndex;
use crate::module::GospelContainer;
use crate::writer::GospelSourceObjectReference;

/// Represents optional debug information about a function
#[derive(Debug, Clone)]
pub struct GospelFunctionDebugData {
    pub source_file_name: String,
    pub instruction_line_numbers: Vec<i32>,
}

/// Represents information about a function
#[derive(Debug, Clone)]
pub struct GospelFunctionData {
    pub function_name: String,
    pub exported: bool,
    pub referenced_strings: Vec<String>,
    pub referenced_functions: Vec<GospelSourceObjectReference>,
    pub max_local_slots: u32,
    pub code: Vec<GospelInstruction>,
    pub debug_data: Option<GospelFunctionDebugData>,
}

/// Allows inspecting contents of the module containers
#[derive(Debug, Clone)]
pub struct GospelContainerReader {
    pub container: GospelContainer,
}
impl GospelContainerReader {
    pub fn container_name(&self) -> anyhow::Result<String> {
        Ok(self.container.strings.get(self.container.header.container_name)?.to_string())
    }
    pub fn container_imports(&self) -> anyhow::Result<Vec<String>> {
        self.container.imports.iter().map(|x| self.container.strings.get(x.container_name).map(|y| y.to_string())).collect()
    }
    fn read_function_reference(&self, reference: GospelObjectIndex) -> anyhow::Result<GospelSourceObjectReference> {
        match reference {
            GospelObjectIndex::Local(function_index) => {
                if function_index as usize >= self.container.functions.len() {
                    bail!("Function index #{} out of bounds", function_index as usize);
                }
                let function_definition = &self.container.functions[function_index as usize];
                let module_name = self.container_name()?;
                let local_name = self.container.strings.get(function_definition.name)?.to_string();
                Ok(GospelSourceObjectReference{module_name, local_name})
            }
            GospelObjectIndex::External(external_function_ref_index) => {
                if external_function_ref_index as usize >= self.container.external_functions.len() {
                    bail!("External function index #{} out of bounds", external_function_ref_index as usize);
                }
                let external_function = &self.container.external_functions[external_function_ref_index as usize];
                if external_function.import_index as usize >= self.container.imports.len() {
                    bail!("External function import index #{} out of bounds", external_function.import_index as usize);
                }
                let module_name = self.container.strings.get(self.container.imports[external_function.import_index as usize].container_name)?.to_string();
                let local_name = self.container.strings.get(external_function.object_name)?.to_string();
                Ok(GospelSourceObjectReference{module_name, local_name})
            }
        }
    }
    fn read_function_data(&self, function_index: usize) -> anyhow::Result<GospelFunctionData> {
        if function_index >= self.container.functions.len() {
            bail!("Function index #{} out of bounds", function_index);
        }
        let function_definition = &self.container.functions[function_index];

        let function_name = self.container.strings.get(function_definition.name)?.to_string();
        let referenced_strings = function_definition.referenced_strings.iter()
            .map(|x| self.container.strings.get(*x).map(|y| y.to_string()))
            .collect::<anyhow::Result<Vec<String>>>()?;
        let referenced_functions = function_definition.referenced_functions.iter()
            .map(|x| self.read_function_reference(*x))
            .collect::<anyhow::Result<Vec<GospelSourceObjectReference>>>()?;

        let debug_data = if let Some(raw_debug_data) = &function_definition.debug_data {
            let source_file_name = self.container.strings.get(raw_debug_data.source_file_name)?.to_string();
            let instruction_line_numbers = raw_debug_data.instruction_line_numbers.clone();
            Some(GospelFunctionDebugData{source_file_name, instruction_line_numbers})
        } else { None };

        Ok(GospelFunctionData{
            function_name,
            exported: function_definition.exported,
            referenced_strings,
            referenced_functions,
            max_local_slots: function_definition.num_slots,
            code: function_definition.code.clone(),
            debug_data,
        })
    }
    pub fn container_functions(&self) -> anyhow::Result<Vec<GospelFunctionData>> {
        (0..self.container.functions.len()).into_iter().map(|function_index| self.read_function_data(function_index)).collect()
    }
    pub fn container_function_by_name(&self, function_name: &str) -> anyhow::Result<Option<GospelFunctionData>> {
        let maybe_function_index = (0..self.container.functions.len()).into_iter().find(|local_function_index| {
            self.container.strings.get(self.container.functions[*local_function_index].name).ok() == Some(function_name)
        });
        if let Some(function_index) = maybe_function_index {
            Ok(Some(self.read_function_data(function_index)?))
        } else { Ok(None) }
    }
}
