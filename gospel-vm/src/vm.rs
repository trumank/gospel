use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use anyhow::{anyhow, bail};
use crate::bytecode::GospelInstruction;
use crate::container::GospelContainer;
use crate::gospel_type::{GospelArch, GospelPlatform, GospelSlotBinding, GospelSlotDefinition, GospelStaticValue, GospelStaticValueType, GospelTypeDefinition, GospelTypeIndex, GospelValueType};

#[derive(Debug, Clone)]
pub struct GospelBaseClassLayout {
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

#[derive(Debug, Clone)]
pub struct GospelMemberLayout {
    pub name: String,
    pub offset: usize,
    pub actual_size: usize,
    pub layout: GospelTypeLayout,
}

/// Represents a fully resolved layout of a particular type
/// This exposes information such as the size of the type, its alignment, unaligned size,
/// and offsets, sizes and full type layouts of its members
#[derive(Debug, Clone, Default)]
pub struct GospelTypeLayout {
    pub name: String,
    pub alignment: usize,
    pub unaligned_size: usize,
    pub size: usize,
    pub base_classes: Vec<GospelBaseClassLayout>,
    pub members: Vec<GospelMemberLayout>,
    pub source_type: Option<GospelVMTypeReference>,
    pub source_args: Option<Vec<GospelVMValue>>,
}

/// Platform config defines the platform which the type layouts are being calculated for
/// This includes the operating system and the processor architecture (and sometimes ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, Clone, Copy)]
pub struct GospelVMPlatformConfig {
    pub platform: GospelPlatform,
    pub arch: GospelArch,
}

/// Represents reference to a particular type located inside a particular container
/// Type cannot be used directly; type instances can be created and their layouts investigated
/// by using GospelVMTypeReference:resolve with the required template arguments
#[derive(Debug, Clone)]
pub struct GospelVMTypeReference {
    container: Rc<GospelVMContainer>,
    type_index: u32,
}
impl GospelVMTypeReference {
    /// Returns the type container which defines this type
    pub fn source_container(&self) -> Rc<GospelVMContainer> {
        self.container.clone()
    }
    /// Returns the name of the type referenced
    pub fn type_name(&self) -> &str {
        self.container.get_type_name(self.type_index)
    }
    /// Attempts to resolve the layout of this type using the arguments provided
    pub fn resolve_layout(&self, args: &Vec<GospelVMValue>) -> anyhow::Result<GospelTypeLayout> {
        self.container.resolve_layout_internal(self.type_index, args)
    }
    fn resolve_layout_static(&self, args: &Vec<GospelStaticValue>) -> anyhow::Result<GospelTypeLayout> {
        self.container.resolve_layout_static(self.type_index, args)
    }
}

/// VM Value represents a value that VM bytecode can read and write
/// Currently supported value types are integers, type references and type layouts
/// Type references can be converted into type layouts by providing them with arguments
#[derive(Debug, Clone)]
pub enum GospelVMValue {
    Integer(i32), // signed 32-bit integer value
    TypeDefinition{ reference: GospelVMTypeReference }, // definition of a type with no template arguments
    TypeLayout{ layout: GospelTypeLayout }, // pre-computed type layout
}

#[derive(Debug)]
struct GospelGlobalStorage {
    initial_value: RefCell<Option<i32>>,
    current_value: RefCell<Option<i32>>,
}

#[derive(Debug)]
struct GospelVMExecutionState {
    pub layout_builder: GospelTypeLayout,
    pub slots: Vec<Option<GospelVMValue>>,
    pub referenced_strings: Vec<String>,
    pub stack: Vec<GospelVMValue>,
}
impl GospelVMExecutionState {
    fn run(state: &mut GospelVMExecutionState, code: &Vec<GospelInstruction>) -> anyhow::Result<GospelTypeLayout> {
        bail!("TODO")
    }
}

#[derive(Debug)]
pub struct GospelVMContainer {
    container: Rc<GospelContainer>,
    external_references: Vec<Rc<GospelVMContainer>>,
    global_lookup_by_id: HashMap<usize, Rc<GospelGlobalStorage>>,
    type_lookup_by_name: HashMap<String, u32>,
}
impl GospelVMContainer {
    /// Returns the name of this type container
    pub fn container_name(&self) -> &str {
        self.container.container_name()
    }
    /// Attempts to find a type with the given name in this container and returns a reference to it
    pub fn find_named_type(self: &Rc<Self>, name: &str) -> Option<GospelVMTypeReference> {
        self.type_lookup_by_name.get(name).map(|type_index| GospelVMTypeReference{
            container: self.clone(), type_index: *type_index })
    }
    fn get_type_name(&self, index: u32) -> &str {
        let type_definition = &self.container.types[index as usize];
        self.container.strings.get(type_definition.type_name)
    }
    fn resolve_type_index(self: &Rc<Self>, type_index: GospelTypeIndex) -> anyhow::Result<GospelVMTypeReference> {
        if type_index.is_external() {
            let external_type = &self.container.external_types[type_index.index() as usize];
            let source_container = &self.external_references[external_type.import_index as usize];
            let type_name = self.container.strings.get(external_type.type_name);
            return source_container.find_named_type(type_name)
                .ok_or_else(|| { anyhow!("Imported named type {} does not exist in container {}", self.container_name(), type_name.to_string()) });
        }
        Ok(GospelVMTypeReference{ container: self.clone(), type_index: type_index.index() })
    }
    fn resolve_static_type_instance_layout(&self, index: u32) -> anyhow::Result<GospelTypeLayout> {
        let type_instance = &self.container.static_instances[index as usize];
        let type_reference = self.resolve_type_index(type_instance.type_index)?;
        type_reference.resolve_layout_static(&type_instance.arguments)
    }
    fn resolve_static_value(&self, value: &GospelStaticValue) -> anyhow::Result<GospelVMValue> {
        match value.value_type {
            GospelValueType::Integer => {
                match value.static_type {
                    GospelStaticValueType::Integer => {
                        Ok(GospelVMValue::Integer(value.data as i32))
                    }
                    _ => bail!("Invalid static initializer for integer value")
                }
            }
            GospelValueType::TypeDefinition => {
                match value.static_type {
                    GospelStaticValueType::TypeDefinition => {
                        let type_index = GospelTypeIndex::create_raw(value.data);
                        let reference = self.resolve_type_index(type_index)?;
                        Ok(GospelVMValue::TypeDefinition {reference})
                    }
                    _ => bail!("Invalid static initializer for type definition")
                }
            }
            GospelValueType::TypeLayout => {
                match value.static_type {
                    GospelStaticValueType::StaticTypeLayout => {
                        let layout = self.resolve_static_type_instance_layout(value.data)?;
                        Ok(GospelVMValue::TypeLayout {layout})
                    }
                    _ => bail!("Invalid static initializer for type layout")
                }
            }
        }
    }
    fn resolve_layout_static(&self, index: u32, args: &Vec<GospelStaticValue>) -> anyhow::Result<GospelTypeLayout> {
        let mut resolved_args: Vec<GospelVMValue> = Vec::new();
        for argument_index in 0..args.len() {
            let resolved_value = self.resolve_static_value(&args[argument_index])
                .map_err(|x| anyhow!("Failed to resolve template argument #{} value: {}", argument_index, x.to_string()))?;
            resolved_args.push(resolved_value)
        }
        self.resolve_layout_internal(index, &resolved_args)
    }
    fn resolve_slot_binding(&self, slot: &GospelSlotDefinition, args: &Vec<GospelVMValue>) -> anyhow::Result<Option<GospelVMValue>> {
        match slot.binding {
            GospelSlotBinding::Uninitialized => {
                Ok(None)
            }
            GospelSlotBinding::StaticValue => {
                if slot.value_type != slot.binding_data.value_type {
                    bail!("Slot value type is not compatible with static value type specified")
                }
                let resolved_value = self.resolve_static_value(&slot.binding_data)?;
                Ok(Some(resolved_value))
            }
            GospelSlotBinding::InputVariableValue => {

            }
        }
    }
    fn resolve_layout_internal(self: &Rc<Self>, index: u32, args: &Vec<GospelVMValue>) -> anyhow::Result<GospelTypeLayout> {
        let type_definition = &self.container.types[index as usize];

        // Construct a fresh VM state
        let mut vm_state = GospelVMExecutionState{
            layout_builder: GospelTypeLayout::default(),
            slots: Vec::with_capacity(type_definition.slots.len()),
            referenced_strings: Vec::with_capacity(type_definition.referenced_strings.len()),
            stack: Vec::new(),
        };

        // Populate slots with their initial values
        for slot_index in 0..type_definition.slots.len() {
            let slot_value = self.resolve_slot_binding(&type_definition.slots[slot_index], args)
            .map_err(|x| {
                let slot_name = self.container.strings.get(type_definition.slots[slot_index].debug_name);
                anyhow!("Failed to bind slot #{} ({}) value: {}", slot_index, slot_name.to_string(), x.to_string())
            })?;
            vm_state.slots.push(slot_value)
        }

        // Populate referenced strings
        for string_index in type_definition.referenced_strings {
            vm_state.referenced_strings.push(self.container.strings.get(string_index).to_string());
        }

        // Populate layout builder with metadata and initial values
        vm_state.layout_builder.name = self.container.strings.get(type_definition.type_name).to_string();
        vm_state.layout_builder.source_type = Some(GospelVMTypeReference{container: self.clone(), type_index: index});
        vm_state.layout_builder.source_args = Some(args.clone());
        vm_state.layout_builder.alignment = 1;

        // Run the VM to evaluate the type now. Note that this can give us a completely different type as well
        GospelVMExecutionState::run(&mut vm_state, &type_definition.code)
    }
}

/// VM state for the Gospel VM
/// Containers can be injected into the VM to register type definitions
/// Global variables can be defined to supply additional information to the type definitions.
/// Type definitions can be retrieved with find_type
/// WARNING: VM instances are NOT thread safe, and must be wrapped into RWLock to be safely usable concurrently
pub struct GospelVMState {
    platform_config: GospelVMPlatformConfig,
    containers: Vec<Rc<GospelVMContainer>>,
    containers_by_name: HashMap<String, Rc<GospelVMContainer>>,
    globals_by_name: HashMap<String, Rc<GospelGlobalStorage>>,
}
impl GospelVMState {

    /// Creates a new, blank VM state with the provided platform config
    /// Type contains must be mounted to the VM by calling mount_container
    fn create(platform_config: GospelVMPlatformConfig) -> Self {
        Self{platform_config, containers: Vec::new(), containers_by_name: HashMap::new(), globals_by_name: HashMap::new()}
    }

    /// Adds a new gospel container to the VM. Returns the created container
    fn mount_container(&mut self, container: GospelContainer) -> anyhow::Result<Rc<GospelVMContainer>> {
        let wrapped_container = Rc::new(container);
        let container_name = wrapped_container.container_name().to_string();
        if self.containers_by_name.get(&container_name).is_some() {
            bail!("Container with name {} is already mounted", container_name);
        }

        // Resolve imports necessary to construct external types down the line
        let mut external_references: Vec<Rc<GospelVMContainer>> = Vec::new();
        for import_index in 0..wrapped_container.imports.len() {
            let import_container_name = wrapped_container.strings.get(wrapped_container.imports[import_index].container_name);
            let resolved_import = self.find_named_container(import_container_name)
                .ok_or_else(|| { anyhow!("Cannot mount container {} because it depends on container {} that is not mounted", container_name, import_container_name) })?;
            external_references.push(resolved_import);
        }

        let mut vm_container = GospelVMContainer{
            container: wrapped_container.clone(),
            external_references,
            global_lookup_by_id: HashMap::new(),
            type_lookup_by_name: HashMap::new()
        };

        // Build lookup table for types by name, and create globals referenced by the container
        for type_index in 0..wrapped_container.types.len() {
            let type_name = wrapped_container.strings.get(wrapped_container.types[type_index].type_name);
            vm_container.type_lookup_by_name.insert(type_name.to_string(), type_index as u32);
        }
        for global_index in 0..wrapped_container.globals.len() {
            let global_name = wrapped_container.strings.get(wrapped_container.globals[global_index].name);
            let initial_value = wrapped_container.globals[global_index].default_value;

            let global_value = self.find_or_create_global(global_name, initial_value)?;
            vm_container.global_lookup_by_id.insert(global_index, global_value);
        }

        // Finally, add container to the mounted container list
        let wrapped_vm_container = Rc::new(vm_container);
        self.containers.push(wrapped_vm_container.clone());
        self.containers_by_name.insert(container_name, wrapped_vm_container.clone());

        Ok(wrapped_vm_container)
    }

    /// Reads the current value of a global variable by name, returns None if variable does not exist or is not currently assigned
    pub fn read_global_value(&self, name: &str) -> Option<i32> {
        self.globals_by_name.get(name).and_then(|x| *x.current_value.borrow())
    }

    /// Assigns the value to the global variable by name. Defines a new global variable if it has not been defined yet
    pub fn set_global_value(&mut self, name: &str, new_value: i32) -> anyhow::Result<()> {
        let global_storage = self.find_or_create_global(name, None)?;
        global_storage.current_value.replace(Some(new_value));
        Ok({})
    }

    /// Returns the type container by name
    pub fn find_named_container(&self, name: &str) -> Option<Rc<GospelVMContainer>> {
        self.containers_by_name.get(name).map(|x| x.clone())
    }

    fn find_or_create_global(&mut self, name: &str, initial_value: Option<i32>) -> anyhow::Result<Rc<GospelGlobalStorage>> {
        if let Some(existing_global) = self.globals_by_name.get(name) {

            if let Some(unwrapped_initial_value) = initial_value {
                let mut current_initial_value = existing_global.initial_value.borrow_mut();

                // Validate that the initial value is the same as the provided one
                if let Some(unwrapped_current_initial_value) = *current_initial_value {
                    if unwrapped_current_initial_value != unwrapped_initial_value {
                        bail!("Incompatible default values for global variable {}: current default value is {}, but new default value is {}",
                            name.to_string(), unwrapped_current_initial_value, unwrapped_initial_value);
                    }
                } else {
                    // Current initial value becomes the new initial value for this variable
                    *current_initial_value = Some(unwrapped_initial_value);

                    // If current value is not set, the new initial value takes over
                    let mut current_value = existing_global.current_value.borrow_mut();
                    if current_value.is_none() {
                        *current_value = Some(unwrapped_initial_value);
                    }
                }
            }
            return Ok(existing_global.clone())
        }

        // Create a new global storage with initial value as the current value
        let new_global = Rc::new(GospelGlobalStorage{
            initial_value: RefCell::new(initial_value),
            current_value: RefCell::new(initial_value),
        });
        self.globals_by_name.insert(name.to_string(), new_global.clone());
        Ok(new_global)
    }
}
