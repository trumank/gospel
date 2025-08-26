use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::{read_to_string};
use std::path::{absolute, Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;
use anyhow::{anyhow, bail};
use fancy_regex::Regex;
use itertools::Itertools;
use semver::{Version, VersionReq};
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;
use gospel_vm::module::GospelContainer;
use crate::backend::{CompilerInstance, CompilerModuleBuilder};
use crate::parser::parse_source_file;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GospelModuleDescriptor {
    pub name: String,
    pub version: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub authors: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct GospelDependencyDescriptor {
    pub version: String,
    #[serde(default)]
    pub path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GospelModuleDefinitionFile {
    pub module: GospelModuleDescriptor,
    #[serde(default)]
    pub dependencies: BTreeMap<String, GospelDependencyDescriptor>,
}

#[derive(Debug, Clone)]
pub struct GospelModule {
    pub definition: GospelModuleDefinitionFile,
    pub version: Version,
    pub module_dir: PathBuf,
    pub source_dir: PathBuf,
    pub resolved_dependencies: RefCell<Vec<Rc<GospelModule>>>,
}
impl GospelModule {
    pub fn module_name(&self) -> &str {
        &self.definition.module.name
    }
    fn collect_source_files(&self, builder: &dyn CompilerModuleBuilder) -> anyhow::Result<()> {
        let mut all_source_files: Vec<PathBuf> = Vec::new();

        // Discover all source files in the module first
        for dir_entry_result in WalkDir::new(&self.source_dir) {
            let dir_entry = dir_entry_result.map_err(|x| anyhow!("Failed to iterate module {} source directory: {}", &self.definition.module.name, x))?;
            if dir_entry.file_type().is_file() && let Some(extension) = dir_entry.path().extension() && extension == "gs" {
                all_source_files.push(dir_entry.path().to_path_buf());
            }
        }
        // Sort files in a consistent order
        all_source_files.sort();

        // Parse source files and add them to the builder
        for source_filename in all_source_files {
            let source_file_contents = read_to_string(&source_filename)
                .map_err(|x| anyhow!("Failed to read module {} source file {}: {}", &self.definition.module.name, source_filename.display(), x))?;
            let parsed_source_file = parse_source_file(&source_filename.file_name().unwrap().to_string_lossy().to_string(), &source_file_contents)
                .map_err(|x| anyhow!("Failed to parse module {} source file {}: {}", &self.definition.module.name, source_filename.display(), x))?;
            builder.add_source_file(parsed_source_file)
                .map_err(|x| anyhow!("Failed to compile module {} source file {}: {}", &self.definition.module.name, source_filename.display(), x))?;
        }
        Ok({})
    }
    pub fn include_module(&self, compiler: &Rc<CompilerInstance>) -> anyhow::Result<()> {
        let module_builder = compiler.declare_module(&self.definition.module.name)
            .map_err(|x| anyhow!("Failed to declare module {}: {}", &self.definition.module.name, x))?;
        self.collect_source_files(&module_builder)?;
        Ok({})
    }
    pub fn compile_module(&self, compiler: &Rc<CompilerInstance>) -> anyhow::Result<GospelContainer> {
        let module_builder = compiler.define_module(&self.definition.module.name)
            .map_err(|x| anyhow!("Failed to declare module {}: {}", &self.definition.module.name, x))?;
        self.collect_source_files(&module_builder)?;
        module_builder.compile().map_err(|x| anyhow!("Failed to compile module {}: {}", &self.definition.module.name, x))
    }
    pub fn get_all_module_dependencies(&self) -> Vec<Rc<GospelModule>> {
        let mut dependency_list: Vec<Rc<GospelModule>> = Vec::new();
        let mut dependency_set: HashSet<String> = HashSet::new();
        self.collect_module_dependencies_recursive(&mut dependency_list, &mut dependency_set);
        dependency_list
    }
    pub fn include_dependencies_and_compile_module(&self, compiler: &Rc<CompilerInstance>) -> anyhow::Result<GospelContainer> {
        let all_module_dependencies = self.get_all_module_dependencies();
        for module_dependency in &all_module_dependencies {
            module_dependency.include_module(compiler)?;
        }
        self.compile_module(compiler)
    }
    pub fn compile_module_tree(&self, compiler: &Rc<CompilerInstance>) -> anyhow::Result<Vec<GospelContainer>> {
        let all_module_dependencies = self.get_all_module_dependencies();
        let mut result_modules: Vec<GospelContainer> = Vec::new();
        for module_dependency in &all_module_dependencies {
            result_modules.push(module_dependency.compile_module(compiler)?);
        }
        result_modules.push(self.compile_module(compiler)?);
        Ok(result_modules)
    }
    pub fn default_build_product_path(&self) -> PathBuf {
        self.module_dir.join("target").join(format!("{}.gso", &self.definition.module.name))
    }
    fn collect_module_dependencies_recursive(&self, dependency_list: &mut Vec<Rc<GospelModule>>, dependency_set: &mut HashSet<String>) {
        for dependency_module in self.resolved_dependencies.borrow().iter() {
            dependency_module.collect_module_dependencies_recursive(dependency_list, dependency_set);
            if !dependency_set.contains(&dependency_module.definition.module.name) {
                dependency_list.push(dependency_module.clone());
                dependency_set.insert(dependency_module.definition.module.name.clone());
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
struct GospelModuleSource {
    module_name: String,
    all_locations: RefCell<HashMap<PathBuf, Rc<GospelModule>>>,
    solver_constraints: RefCell<Vec<VersionReq>>,
    resolved_module: RefCell<Option<Rc<GospelModule>>>,
}

#[derive(Debug)]
struct GospelModuleResolver {
    modules: HashMap<String, Rc<GospelModuleSource>>,
    root_modules: Vec<Rc<GospelModule>>,
    modules_pending_solve: Vec<String>,
}
impl GospelModuleResolver {
    fn discover_modules_recursive(&mut self, root_module_paths: &Vec<PathBuf>) -> anyhow::Result<()> {
        let mut module_stack: Vec<String> = Vec::new();
        module_stack.push(String::from("<root modules>"));
        for module_path in root_module_paths {
            let module_descriptor = self.resolve_module_internal(module_path, None, &mut module_stack)?;
            self.root_modules.push(module_descriptor);
        }
        Ok({})
    }
    fn solve_module_dependencies(&mut self) -> anyhow::Result<()> {
        for root_module in self.root_modules.clone() {
            *self.modules.get(&root_module.definition.module.name).unwrap().resolved_module.borrow_mut() = Some(root_module.clone());
            self.add_module_dependencies(&root_module)?;
        }
        while let Some(pending_module_name) = self.modules_pending_solve.pop() {
            let module_source = self.modules.get(&pending_module_name).unwrap().clone();
            let resolved_module = self.solve_module_version(&module_source)?;
            *module_source.resolved_module.borrow_mut() = Some(resolved_module.clone());
            self.add_module_dependencies(&resolved_module)?;
        }
        Ok({})
    }
    fn collect_module_dependencies(&mut self) -> anyhow::Result<()> {
        for module_source in self.modules.values() {
            if let Some(result_module) = module_source.resolved_module.borrow().clone() {
                for dependency_name in result_module.definition.dependencies.keys() {
                    if let Some(resolved_dependency) = self.modules.get(dependency_name).and_then(|x| x.resolved_module.borrow().clone()) {
                        result_module.resolved_dependencies.borrow_mut().push(resolved_dependency);
                    } else {
                        bail!("Failed to resolve dependency {} of module {}", dependency_name, &result_module.definition.module.name);
                    }

                }
            }
        }
        Ok({})
    }
    fn solve_module_version(&mut self, module_source: &Rc<GospelModuleSource>) -> anyhow::Result<Rc<GospelModule>> {
        module_source.all_locations.borrow().values()
            .sorted_by(|module_a, module_b| module_a.version.cmp(&module_b.version).reverse())
            .find(|module| module_source.solver_constraints.borrow().iter().all(|constraint| constraint.matches(&module.version)))
            .cloned()
            .ok_or_else(|| anyhow!("Failed to find version of module {} that satisfies all version constraints", &module_source.module_name))
    }
    fn add_module_dependencies(&mut self, module: &Rc<GospelModule>) -> anyhow::Result<()> {
        for (dependency_name, dependency_descriptor) in &module.definition.dependencies {
            let dependency_constraint = VersionReq::parse(&dependency_descriptor.version)
                .map_err(|x| anyhow!("Failed to parse module {} dependency range on module {}: {}", &module.definition.module.name, dependency_name, x))?;
            self.add_module_dependency_constraint(dependency_name, &dependency_constraint, &module.definition.module.name)?;
        }
        Ok({})
    }
    fn add_module_dependency_constraint(&mut self, dependency_name: &String, constraint: &VersionReq, dependent_module_name: &str) -> anyhow::Result<()> {
        let module_source = self.modules.get(dependency_name)
            .ok_or_else(|| anyhow!("Failed to module {} (required by {}). Make sure dependency path is specified or it is explicitly provided as a root module", dependency_name, dependent_module_name))?;

        if let Some(resolved_module) = module_source.resolved_module.borrow().clone() {
            if constraint.matches(&resolved_module.version) {
                bail!("Dependency resolution error: Module {} requires module {} version range {}, but dependency version previously selected is {}", dependent_module_name, dependency_name, constraint, &resolved_module.version);
            }
        } else {
            module_source.solver_constraints.borrow_mut().push(constraint.clone());
            if !self.modules_pending_solve.contains(dependency_name) {
                self.modules_pending_solve.push(dependency_name.clone());
            }
        }
        Ok({})
    }
    fn resolve_module_internal(&mut self, module_path: &Path, expected_module_name: Option<&str>, module_stack: &mut Vec<String>) -> anyhow::Result<Rc<GospelModule>> {
        let referenced_by_string = module_stack.join(" -> ");
        let absolute_module_path = absolute(module_path)
            .map_err(|x| anyhow!("Module directory {} does not exist: {} (referenced by {})", module_path.display(), x, &referenced_by_string))?;

        let module_file_path = absolute_module_path.join(PathBuf::from("Gospel.toml"));
        if !module_file_path.is_file() {
            bail!("Failed to find gospel module descriptor file at {} (referenced by {})", module_file_path.display(), &referenced_by_string);
        }
        let module_file_contents = read_to_string(&module_file_path)
            .map_err(|x| anyhow!("Failed to read gospel module descriptor file at {}: {} (referenced by {})", module_file_path.display(), x, &referenced_by_string))?;
        let module_definition: GospelModuleDefinitionFile = toml::from_str(&module_file_contents)
            .map_err(|x| anyhow!("Failed to parse gospel module descriptor file at {}: {} (referenced by {})", module_file_path.display(), x, &referenced_by_string))?;

        let module_name = module_definition.module.name.clone();
        let module_name_pattern = Regex::from_str("[A-Za-z0-9-_$]+")?;
        if !module_name_pattern.is_match(&module_name)? {
            bail!("Module name '{}' is invalid: Only alphanumeric characters, as well as dashes, underscores and dollar sign, are allowed in module names", module_name);
        }
        if module_stack.contains(&module_name) {
            bail!("Cyclic dependency on module {}: (referenced by {})", &module_name, &referenced_by_string);
        }
        if let Some(check_module_name) = expected_module_name && check_module_name != module_definition.module.name {
            bail!("Module name mismatch: dependency listed module with name {}, but actual module name is {} (referenced by {})", &check_module_name, module_name, &referenced_by_string);
        }

        // Check if there is already an existing module at this absolute path
        let module_source = self.modules.entry(module_name.clone()).or_insert_with(||
            Rc::new(GospelModuleSource{module_name: module_name.clone(), ..GospelModuleSource::default()})).clone();
        if let Some(existing_module) = module_source.all_locations.borrow().get(&absolute_module_path) {
            return Ok(existing_module.clone());
        }

        let module_version = Version::parse(&module_definition.module.version)
            .map_err(|x| anyhow!("Failed to parse module {} version: {} (referenced by {})", &module_name, x, &referenced_by_string))?;
        // Make sure module source directory exists
        let module_source_dir = absolute_module_path.join("src");
        if !module_source_dir.is_dir() {
            bail!("Module {} does not have source directory {} (referenced by {})", module_name, module_source_dir.display(), &referenced_by_string);
        }
        let result_module = Rc::new(GospelModule{definition: module_definition.clone(), version: module_version, module_dir: absolute_module_path.clone(),
            source_dir: module_source_dir, resolved_dependencies: RefCell::new(Vec::new())});
        module_source.all_locations.borrow_mut().insert(absolute_module_path.clone(), result_module.clone());

        // Resolve module dependencies
        module_stack.push(module_name.clone());
        for (dependency_module_name, dependency_descriptor) in &module_definition.dependencies {
            if !dependency_descriptor.path.is_empty() {
                let dependency_path = absolute_module_path.join(&dependency_descriptor.path);
                self.resolve_module_internal(&dependency_path, Some(dependency_module_name.as_str()), module_stack)
                    .map_err(|x| anyhow!("Failed to resolve module {} dependency {}: {} (referenced by {})", module_name, dependency_module_name, x, &referenced_by_string))?;
            }
        }
        module_stack.pop();

        Ok(result_module)
    }
}

/// Resolves module dependency graph given the list of module paths
pub fn resolve_module_dependencies(root_module_paths: &Vec<PathBuf>) -> anyhow::Result<Vec<Rc<GospelModule>>> {
    let mut new_resolver = GospelModuleResolver{modules: HashMap::new(), root_modules: Vec::new(), modules_pending_solve: Vec::new()};
    new_resolver.discover_modules_recursive(root_module_paths)?;
    new_resolver.solve_module_dependencies()?;
    new_resolver.collect_module_dependencies()?;
    Ok(new_resolver.root_modules)
}
