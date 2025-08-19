use std::cell::Cell;
use std::cmp::{max, min};
use std::collections::HashMap;
use std::str::FromStr;
use anyhow::{anyhow, bail};
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};

/// Aligns the value up to the nearest multiple of the alignment
pub fn align_value(value: usize, align: usize) -> usize {
    let reminder = if align == 0 { 0 } else { value % align };
    if reminder == 0 { value } else { value + (align - reminder) }
}

/// Corresponds to <arch> in LLVM target triplet
/// Architecture determines the instruction set and, sometimes, the calling convention used (combined with sys)
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetArchitecture {
    X86_64,
    ARM64,
    ARM64EC,
}
impl TargetArchitecture {
    /// Returns the architecture current binary has been compiled for (if it can be represented)
    pub fn current_arch() -> Option<TargetArchitecture> {
        match std::env::consts::ARCH {
            "x86_64" => Some(TargetArchitecture::X86_64),
            "aarch64" => Some(TargetArchitecture::ARM64),
            _ => None,
        }
    }
}

/// Corresponds to <sys> in LLVM target triplet
/// Target system generally defines calling convention used and object file format
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetOperatingSystem {
    None,
    Win32,
    Linux,
    Darwin,
}
impl TargetOperatingSystem {
    /// Returns the OS the binary has been compiled for (if it can be represented)
    pub fn current_os() -> Option<TargetOperatingSystem> {
        match std::env::consts::OS {
            "windows" => Some(TargetOperatingSystem::Win32),
            "linux" => Some(TargetOperatingSystem::Linux),
            "android" => Some(TargetOperatingSystem::Linux),
            "macos" => Some(TargetOperatingSystem::Darwin),
            "ios" => Some(TargetOperatingSystem::Darwin),
            _ => None,
        }
    }
    /// Returns the default environment for the OS in question. Returns none for bare metal
    pub fn default_env(self) -> Option<TargetEnvironment> {
        match self {
            TargetOperatingSystem::None => None,
            TargetOperatingSystem::Win32 => Some(TargetEnvironment::MSVC),
            TargetOperatingSystem::Linux => Some(TargetEnvironment::Gnu),
            TargetOperatingSystem::Darwin => Some(TargetEnvironment::Macho),
        }
    }
}

/// Corresponds to <env> in LLVM target triplet
/// Target env determines the ABI rules used for type layout calculation, for example semantics used for C++ class inheritance and exception handling
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumString, Serialize, Deserialize)]
pub enum TargetEnvironment {
    MSVC,
    Gnu,
    Macho,
}

/// Target triplet defines the target which the type layouts are being calculated for
/// This includes the operating system, the processor architecture, and environment (ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct TargetTriplet {
    pub arch: TargetArchitecture,
    pub sys: TargetOperatingSystem,
    pub env: TargetEnvironment,
}
impl TargetTriplet {
    /// Returns the address size for the provided target triplet
    pub fn address_size(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    /// Returns the size of the "long" type for the provided target triplet
    pub fn long_size(&self) -> usize {
        // 4 on Win32, 8 on everything else
        if self.sys == TargetOperatingSystem::Win32 { 4 } else { 8 }
    }
    /// Returns the size of the "wchar_t" type for the provided target triplet
    pub fn wide_char_size(&self) -> usize {
        // 2 on Win32, 4 on everything else
        if self.sys == TargetOperatingSystem::Win32 { 2 } else { 4 }
    }
    pub fn uses_aligned_base_class_size(&self) -> bool {
        self.env == TargetEnvironment::MSVC // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
    /// Returns the target that the current executable has been compiled for
    pub fn current_target() -> Option<TargetTriplet> {
        let current_arch = TargetArchitecture::current_arch();
        let current_os = TargetOperatingSystem::current_os();
        let default_env = current_os.as_ref().and_then(|x| x.default_env());

        if current_arch.is_none() || current_os.is_none() || default_env.is_none() {
            None
        } else { Some(TargetTriplet {
            arch: current_arch.unwrap(),
            sys: current_os.unwrap(),
            env: default_env.unwrap(),
        }) }
    }
    pub fn parse(triplet_str: &str) -> anyhow::Result<TargetTriplet> {
        let splits: Vec<&str> = triplet_str.split('-').collect();
        if splits.len() < 2 {
            bail!("Target triplet string too short, need at least 2 parts (<arch>-<os>)");
        }
        if splits.len() > 3 {
            bail!("Target triplet string too long, should consist of at most 3 parts (<arch>-<os>-<env>)");
        }
        let arch = TargetArchitecture::from_str(splits[0])
            .map_err(|x| anyhow!("Failed to parse arch: {}", x.to_string()))?;
        let sys = TargetOperatingSystem::from_str(splits[1])
            .map_err(|x| anyhow!("Failed to parse OS: {}", x.to_string()))?;
        let env = if splits.len() >= 3 {
            TargetEnvironment::from_str(splits[2])
                .map_err(|x| anyhow!("Failed to parse env: {}", x.to_string()))?
        } else {
            sys.default_env().ok_or_else(|| anyhow!("Default env for OS not available please specify env manually (<arch>-<os>-<env>)"))?
        };
        Ok(TargetTriplet {arch, sys, env})
    }
}

fn fork_type_graph_internal<'a, T : TypeGraphLike<'a>>(graph: &'a T, type_index: usize, result: &mut TypeTree, type_lookup: &mut HashMap<usize, usize>) -> usize {
    if let Some(existing_index) = type_lookup.get(&type_index) {
        return *existing_index
    }
    // Need to add the placeholder type to reserve the slot while potentially processing subtypes
    let new_index = result.types.len();
    result.types.push(Type::Primitive(PrimitiveType::Void));
    type_lookup.insert(type_index, new_index);

    let copied_type = match graph.type_by_index(type_index) {
        Type::Pointer(pointer_type) => Type::Pointer(PointerType{pointee_type_index: fork_type_graph_internal(graph, pointer_type.pointee_type_index, result, type_lookup), is_reference: pointer_type.is_reference}),
        Type::Array(array_type) => Type::Array(ArrayType{element_type_index: fork_type_graph_internal(graph, array_type.element_type_index, result, type_lookup), array_length: array_type.array_length}),
        Type::CVQualified(cv_qualified_type) => Type::CVQualified(CVQualifiedType{base_type_index: fork_type_graph_internal(graph, cv_qualified_type.base_type_index, result, type_lookup), constant: cv_qualified_type.constant, volatile: cv_qualified_type.volatile}),
        Type::Primitive(primitive_type) => Type::Primitive(primitive_type.clone()),
        Type::Function(function_type) => {
            let return_value_type_index = fork_type_graph_internal(graph, function_type.return_value_type_index, result, type_lookup);
            let this_type_index = if let Some(value) = function_type.this_type_index { Some(fork_type_graph_internal(graph, value, result, type_lookup)) } else { None };
            let mut argument_type_indices: Vec<usize> = Vec::new();
            for argument_type_index in &function_type.argument_type_indices {
                argument_type_indices.push(fork_type_graph_internal(graph, *argument_type_index, result, type_lookup))
            }
            Type::Function(FunctionType{return_value_type_index, this_type_index, argument_type_indices})
        },
        Type::UDT(user_defined_type) => {
            let mut base_class_indices: Vec<usize> = Vec::new();
            for base_class_index in &user_defined_type.base_class_indices {
                base_class_indices.push(fork_type_graph_internal(graph, *base_class_index, result, type_lookup))
            }
            let mut members: Vec<UserDefinedTypeMember> = Vec::new();
            for member in &user_defined_type.members {
                members.push(match member {
                    UserDefinedTypeMember::Field(field) => {
                        let member_type_index = fork_type_graph_internal(graph, field.member_type_index, result, type_lookup);
                        UserDefinedTypeMember::Field(UserDefinedTypeField{name: field.name.clone(), user_alignment: field.user_alignment, member_type_index})
                    },
                    UserDefinedTypeMember::Bitfield(bitfield) => UserDefinedTypeMember::Bitfield(bitfield.clone()),
                    UserDefinedTypeMember::VirtualFunction(function_declaration) => {
                        let return_value_type_index = fork_type_graph_internal(graph, function_declaration.return_value_type_index, result, type_lookup);
                        let mut parameters: Vec<FunctionParameterDeclaration> = Vec::new();
                        for function_parameter in &function_declaration.parameters {
                            let parameter_type_index = fork_type_graph_internal(graph, function_parameter.parameter_type_index, result, type_lookup);
                            parameters.push(FunctionParameterDeclaration{parameter_name: function_parameter.parameter_name.clone(), parameter_type_index});
                        }
                        UserDefinedTypeMember::VirtualFunction(FunctionDeclaration {name: function_declaration.name.clone(), return_value_type_index, parameters,
                            is_const_member_function: function_declaration.is_const_member_function, is_virtual_function_override: function_declaration.is_virtual_function_override})
                    }
                });
            }
            Type::UDT(UserDefinedType{kind: user_defined_type.kind.clone(), name: user_defined_type.name.clone(),
                user_alignment: user_defined_type.user_alignment, member_pack_alignment: user_defined_type.member_pack_alignment, base_class_indices, members})
        }
    };
    result.types[new_index] = copied_type;
    new_index
}

/// Common trait for all type graph-like structs
pub trait TypeGraphLike<'a> {
    /// Returns the type at the specified index in the type graph
    fn type_by_index(self: &'a Self, type_index: usize) -> &'a Type;

    /// Creates an isolated type tree describing the type at the given index and its dependencies
    fn type_tree(self: &'a Self, type_index: usize) -> TypeTree where Self: Sized {
        let mut result = TypeTree{types: Vec::new(), root_type_index: 0};
        let mut type_lookup: HashMap<usize, usize> = HashMap::new();
        let root_type_index = fork_type_graph_internal(self, type_index, &mut result, &mut type_lookup);
        result.root_type_index = root_type_index;
        result
    }
}

/// Represents a primitive type with a target-dependent or fixed size
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, EnumString, Display)]
pub enum PrimitiveType {
    Void,
    Char,
    UnsignedChar,
    WideChar,
    ShortInt,
    UnsignedShortInt,
    Int,
    UnsignedInt,
    Float,
    Double,
    Bool,
    LongInt,
    UnsignedLongInt,
    LongLongInt,
    UnsignedLongLongInt,
    Char8,
    Char16,
    Char32,
}
impl PrimitiveType {
    /// Returns the size and the alignment of this type for the given target triplet
    pub fn size_and_alignment(self, target_triplet: &TargetTriplet) -> usize {
        match self {
            PrimitiveType::Void => 0,
            PrimitiveType::Char => 1,
            PrimitiveType::UnsignedChar => 1,
            PrimitiveType::WideChar => target_triplet.wide_char_size(),
            PrimitiveType::ShortInt => 2,
            PrimitiveType::UnsignedShortInt => 2,
            PrimitiveType::Int => 4,
            PrimitiveType::UnsignedInt => 4,
            PrimitiveType::Float => 4,
            PrimitiveType::Double => 8,
            PrimitiveType::Bool => 1,
            PrimitiveType::LongInt => target_triplet.long_size(),
            PrimitiveType::UnsignedLongInt => target_triplet.long_size(),
            PrimitiveType::LongLongInt => 8,
            PrimitiveType::UnsignedLongLongInt => 8,
            PrimitiveType::Char8 => 1,
            PrimitiveType::Char16 => 1,
            PrimitiveType::Char32 => 1,
        }
    }
}

/// Represents a statically sized array type. Size of the array type is the size of the element type multiplied by the array length
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArrayType {
    /// Index of the element type for this array
    pub element_type_index: usize,
    /// Length of this array type
    pub array_length: usize,
}
impl ArrayType {
    /// Returns the array element type
    pub fn element_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> &'a Type {
        type_graph.type_by_index(self.element_type_index)
    }
    /// Returns the size of the array type
    pub fn size<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        let element_type = self.element_type(type_graph);
        element_type.size(type_graph, target_triplet) * self.array_length
    }
    /// Returns the alignment of the array type
    pub fn alignment<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        let element_type = self.element_type(type_graph);
        element_type.alignment(type_graph, target_triplet)
    }
}

/// Represents an intrinsic pointer type with a known pointee type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PointerType {
    /// Index of the pointee type for this pointer
    pub pointee_type_index: usize,
    /// True if this pointer is a C++ reference
    pub is_reference: bool,
}
impl PointerType {
    /// Returns the pointee type for the pointer type
    pub fn pointee_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> &'a Type {
        type_graph.type_by_index(self.pointee_type_index)
    }
    /// Returns the size and alignment of the pointer type
    pub fn size_and_alignment(&self, target_triplet: &TargetTriplet) -> usize {
        target_triplet.address_size()
    }
}

/// Represents a field in a user defined type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UserDefinedTypeField {
    /// Name of this member if set
    pub name: Option<String>,
    /// User requested alignment for this member, if present
    pub user_alignment: Option<usize>,
    /// Index of the type for this member
    pub member_type_index: usize,
}
impl UserDefinedTypeField {
    /// Returns the type of this member
    pub fn member_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> &'a Type {
        type_graph.type_by_index(self.member_type_index)
    }
}

/// Represents a bitfield in a user defined type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UserDefinedTypeBitfield {
    /// Name of this member if set
    pub name: Option<String>,
    /// Primitive type for this bitfield
    pub primitive_type: PrimitiveType,
    /// Width of this bitfield. Bitfield width cannot exceed the width of the primitive type
    pub bitfield_width: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct FunctionParameterDeclaration {
    /// Index of the parameter type
    pub parameter_type_index: usize,
    /// Optionally specified name of the function parameter
    pub parameter_name: Option<String>,
}

/// Represents a signature of an unique function
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub name: String,
    pub return_value_type_index: usize,
    pub parameter_type_indices: Vec<usize>,
    pub is_const_member_function: bool,
}

/// Represents a function declaration
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct FunctionDeclaration {
    /// Name of the function
    pub name: String,
    /// Index of the function return value type
    pub return_value_type_index: usize,
    /// Parameter declarations for the function
    pub parameters: Vec<FunctionParameterDeclaration>,
    /// True if this is a const member function
    pub is_const_member_function: bool,
    /// True if this function declaration has been marked as a virtual function override
    pub is_virtual_function_override: bool,
}
impl FunctionDeclaration {
    /// Retrieves the signature from this function declaration
    pub fn function_signature(&self) -> FunctionSignature {
        FunctionSignature{name: self.name.clone(), return_value_type_index: self.return_value_type_index, is_const_member_function: self.is_const_member_function,
            parameter_type_indices: self.parameters.iter().map(|x| x.parameter_type_index).collect()}
    }
}

/// Represents type member in a user defined type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UserDefinedTypeMember {
    Field(UserDefinedTypeField),
    Bitfield(UserDefinedTypeBitfield),
    VirtualFunction(FunctionDeclaration),
}
impl UserDefinedTypeMember {
    /// Returns the name of this member (if set)
    pub fn name(&self) -> Option<&str> {
        match self {
            UserDefinedTypeMember::Field(field) => field.name.as_deref(),
            UserDefinedTypeMember::Bitfield(bitfield) => bitfield.name.as_deref(),
            UserDefinedTypeMember::VirtualFunction(virtual_function) => Some(virtual_function.name.as_str()),
        }
    }
}

/// Represents a resolved layout for a member of an UDT type for a particular target triplet
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedUDTFieldLayout {
    pub offset: usize,
    pub alignment: usize,
    pub size: usize,
}

/// Represents a resolved layout for a member of an UDT type for a particular target triplet
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedUDTBitfieldLayout {
    pub offset: usize,
    pub size: usize,
    pub bitfield_offset: usize,
    pub bitfield_width: usize,
}

/// Represents resolved information about a virtual function position in virtual function table of the class
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedUDTVirtualFunctionLocation {
    /// Offset of the vtable from the start of the UDT
    pub vtable_offset: usize,
    /// Offset from the start of the virtual function table
    pub offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResolvedUDTMemberLayout {
    Field(ResolvedUDTFieldLayout),
    Bitfield(ResolvedUDTBitfieldLayout),
    VirtualFunction(ResolvedUDTVirtualFunctionLocation),
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedUDTVtableLayout {
    pub offset: usize,
    pub slot_size: usize,
    pub size: usize,
}

/// Represents a resolved layout of a user defined type for a particular target triplet
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedUDTLayout {
    pub alignment: usize,
    pub unaligned_size: usize,
    pub size: usize,
    pub vtable: Option<ResolvedUDTVtableLayout>,
    #[serde(skip, default)]
    pub virtual_function_lookup: HashMap<FunctionSignature, ResolvedUDTVirtualFunctionLocation>,
    pub base_class_offsets: Vec<usize>,
    pub member_layouts: Vec<ResolvedUDTMemberLayout>,
}

/// Represents a kind of the user defined type, which could be a struct, class, or a union
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize, Display, EnumString)]
pub enum UserDefinedTypeKind {
    #[default]
    Struct,
    Class,
    Union,
}

/// Represents a user defined struct, class or union type, with optional base classes and fields defined in it
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct UserDefinedType {
    /// Kind of the user defined type
    pub kind: UserDefinedTypeKind,
    /// Name of this user defined type if set
    pub name: Option<String>,
    /// User requested alignment for this UDT, if present
    pub user_alignment: Option<usize>,
    /// Pack alignment for this UDT, if present. Pack alignment overrides the maximum alignment that struct members can have
    pub member_pack_alignment: Option<usize>,
    /// Indices of the base class types for this UDT
    pub base_class_indices: Vec<usize>,
    /// All members defined in this UDT
    pub members: Vec<UserDefinedTypeMember>,
}
impl UserDefinedType {
    /// Resolved the layout of this user defined type for a particular target triplet
    pub fn layout<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> ResolvedUDTLayout {
        let current_size: Cell<usize> = Cell::new(0);
        let current_alignment: Cell<usize> = Cell::new(max(1, self.user_alignment.unwrap_or(0)));

        let mut base_class_offsets: Vec<usize> = Vec::new();
        let mut vtable_layout: Option<ResolvedUDTVtableLayout> = None;
        let mut vtable_function_start_offset: usize = 0;
        let mut virtual_function_lookup: HashMap<FunctionSignature, ResolvedUDTVirtualFunctionLocation> = HashMap::new();

        let calculate_member_offset = |member_size: usize, member_alignment: usize| -> usize {
            let capped_member_alignment = self.member_pack_alignment.map(|pack_alignment| min(member_alignment, pack_alignment)).unwrap_or(member_alignment);
            if self.kind != UserDefinedTypeKind::Union {
                current_size.set(align_value(current_size.get(), capped_member_alignment));
            }
            current_alignment.set(max(current_alignment.get(), capped_member_alignment));
            if self.kind == UserDefinedTypeKind::Union {
                current_size.get()
            } else {
                let result_member_offset = current_size.get();
                current_size.set(current_size.get() + member_size);
                result_member_offset
            }
        };

        // TODO: Having base classes or virtual functions in a union should result in type layout error
        let base_class_layouts: Vec<ResolvedUDTLayout> = self.base_class_indices.iter()
            .map(|x| type_graph.type_by_index(*x))
            .filter_map(|x| if let Type::UDT(base_class) = x { Some(base_class) } else { None })
            .map(|x| x.layout(type_graph, target_triplet))
            .collect();
        let has_inherited_vtable = !base_class_layouts.is_empty() && base_class_layouts[0].vtable.is_some();

        // Calculate number of virtual function declarations that are not overrides of the parent virtual functions
        let mut unique_virtual_function_count: usize = 0;
        for member in &self.members {
            if let UserDefinedTypeMember::VirtualFunction(virtual_function) = member {
                let function_signature = virtual_function.function_signature();
                if !virtual_function.is_virtual_function_override && !base_class_layouts.iter().any(|base_class| base_class.virtual_function_lookup.contains_key(&function_signature)) {
                    unique_virtual_function_count += 1;
                }
            }
        }

        // Allocate space in the layout for the virtual function table or extend
        if has_inherited_vtable || unique_virtual_function_count > 0 {
            if !has_inherited_vtable {
                // Virtual function table is not inherited from the first base class, need to allocate space for it
                let size_and_alignment = target_triplet.address_size();
                vtable_function_start_offset = calculate_member_offset(size_and_alignment, size_and_alignment);
                let slot_size = target_triplet.address_size();
                vtable_layout = Some(ResolvedUDTVtableLayout{offset: vtable_function_start_offset, slot_size, size: slot_size * unique_virtual_function_count});

            } else {
                // Virtual function table is inherited from the base class, no need to allocate extra space for it. We still need to adjust the size to account for extra functions though
                let inherited_vtable = base_class_layouts[0].vtable.as_ref().unwrap();
                vtable_function_start_offset = inherited_vtable.size;
                let combined_vtable_size = inherited_vtable.size + inherited_vtable.slot_size * unique_virtual_function_count;
                vtable_layout = Some(ResolvedUDTVtableLayout{offset: inherited_vtable.offset, slot_size: inherited_vtable.slot_size, size: combined_vtable_size});
            }
        }

        // Layout base classes sequentially
        for base_class in &base_class_layouts {
            let base_class_alignment = base_class.alignment;
            let base_class_size = if target_triplet.uses_aligned_base_class_size() { base_class.size } else { base_class.unaligned_size };

            let base_class_offset = calculate_member_offset(base_class_size, base_class_alignment);
            base_class_offsets.push(base_class_offset);

            // Add virtual functions defined in this base class to the lookup and adjust their vtable offset by the offset of the base class within this class
            for (virtual_function_signature, base_class_virtual_function_location) in &base_class.virtual_function_lookup {
                if !virtual_function_lookup.contains_key(virtual_function_signature) {
                    let virtual_function_location = ResolvedUDTVirtualFunctionLocation{vtable_offset: base_class_offset + base_class_virtual_function_location.vtable_offset, offset: base_class_virtual_function_location.offset};
                    virtual_function_lookup.insert(virtual_function_signature.clone(), virtual_function_location);
                }
            }
        }

        // Layout fields in memory sequentially or in parallel, merging multiple bitfields into the single field when possible
        let mut member_layouts: Vec<ResolvedUDTMemberLayout> = Vec::with_capacity(self.members.len());
        let mut current_unique_virtual_function_index: usize = 0;

        for member_index in 0..self.members.len() {
            let member = &self.members[member_index];
            
            if let UserDefinedTypeMember::VirtualFunction(virtual_function) = member {
                // TODO: Having a virtual function in a union should result in type layout error
                let function_signature = virtual_function.function_signature();
                if let Some(override_virtual_function_location) = virtual_function_lookup.get(&function_signature) {
                    // This is an override of a virtual function from the base class(es), do not add the entry but forward to the existing location
                    member_layouts.push(ResolvedUDTMemberLayout::VirtualFunction(override_virtual_function_location.clone()));
                } else if !virtual_function.is_virtual_function_override {
                    // This is a unique virtual function definition and not an override, so add the entry to the vtable
                    let virtual_function_offset = vtable_function_start_offset + vtable_layout.as_ref().unwrap().slot_size * current_unique_virtual_function_index;
                    current_unique_virtual_function_index += 1;
                    let result_location = ResolvedUDTVirtualFunctionLocation{ vtable_offset: vtable_layout.as_ref().unwrap().offset, offset: virtual_function_offset };
                    virtual_function_lookup.insert(function_signature, result_location.clone());
                    member_layouts.push(ResolvedUDTMemberLayout::VirtualFunction(result_location));
                } else {
                    // This is an override of a function that does not exist.
                    // TODO: Throw a type layout error here instead of outputting invalid location
                    let result_location = ResolvedUDTVirtualFunctionLocation{ vtable_offset: usize::MAX, offset: usize::MAX };
                    member_layouts.push(ResolvedUDTMemberLayout::VirtualFunction(result_location));
                }
            } else if let UserDefinedTypeMember::Field(field) = member {
                let member_type = field.member_type(type_graph);
                let member_alignment = max(1, max(member_type.alignment(type_graph, target_triplet), field.user_alignment.unwrap_or(0)));
                let member_size = member_type.size(type_graph, target_triplet);

                let member_offset = calculate_member_offset(member_size, member_alignment);
                let result_layout = ResolvedUDTFieldLayout{ offset: member_offset, alignment: member_alignment, size: member_size };
                member_layouts.push(ResolvedUDTMemberLayout::Field(result_layout));

            } else if let UserDefinedTypeMember::Bitfield(bitfield) = member {
                // If this is a bitfield, and the previous member has the same type and alignment as this one, and is also a bitfield, and has enough space to fit this bitfield in it,
                // copy the offset and other data from the previous field but update the bitfield location to point to this bitfield
                let maximum_bitfield_width = bitfield.primitive_type.size_and_alignment(target_triplet) * 8;
                if member_index > 0 && 
                    let ResolvedUDTMemberLayout::Bitfield(previous_bitfield) = &member_layouts[member_index - 1] &&
                    let bitfield_start_offset = previous_bitfield.bitfield_offset + previous_bitfield.bitfield_width &&
                    (bitfield_start_offset + bitfield.bitfield_width) <= maximum_bitfield_width {
                    
                    let result_layout = ResolvedUDTBitfieldLayout{ offset: previous_bitfield.offset, size: previous_bitfield.size, bitfield_offset: bitfield_start_offset, bitfield_width: bitfield.bitfield_width };
                    member_layouts.push(ResolvedUDTMemberLayout::Bitfield(result_layout));
                } else {
                    let member_size_and_alignment = bitfield.primitive_type.size_and_alignment(target_triplet);

                    let member_offset = calculate_member_offset(member_size_and_alignment, member_size_and_alignment);
                    let result_layout = ResolvedUDTBitfieldLayout{ offset: member_offset, size: member_size_and_alignment, bitfield_offset: 0, bitfield_width: min(bitfield.bitfield_width, maximum_bitfield_width) };
                    member_layouts.push(ResolvedUDTMemberLayout::Bitfield(result_layout));
                }
            }
        }

        // Struct size cannot be zero, it has to be at least 1 byte even for empty structs
        if current_size.get() == 0 {
            current_size.set(1);
        }
        // Align the size to the class alignment now
        let unaligned_size = current_size.get();
        current_size.set(align_value(current_size.get(), current_alignment.get()));
        ResolvedUDTLayout{alignment: current_alignment.get(), unaligned_size, size: current_size.get(), vtable: vtable_layout, virtual_function_lookup, base_class_offsets, member_layouts}
    }
}

/// Represents a type with CV qualifiers applied on top
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct CVQualifiedType {
    /// Index of the base type for this CV-qualified type
    pub base_type_index: usize,
    /// Whenever this type is marked as constant
    pub constant: bool,
    /// Whenever this type is marked as volatile
    pub volatile: bool,
}
impl CVQualifiedType {
    /// Returns the base type for this CV-qualified type
    pub fn base_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> &'a Type {
        type_graph.type_by_index(self.base_type_index)
    }
    /// Returns the size of this CV-qualified type
    pub fn size<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        self.base_type(type_graph).size(type_graph, target_triplet)
    }
    /// Returns the alignment of this CV-qualified type
    pub fn alignment<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        self.base_type(type_graph).alignment(type_graph, target_triplet)
    }
}

/// Represents a type of the function signature. Function type does not have a size, and must be wrapped in a pointer type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct FunctionType {
    /// Index of the return value type for this function type
    pub return_value_type_index: usize,
    /// When set, this function type is a member function, and this is a type of the "this" argument
    pub this_type_index: Option<usize>,
    /// Type indices of the function arguments
    pub argument_type_indices: Vec<usize>,
}
impl FunctionType {
    /// Returns this argument type for the function type
    pub fn this_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> Option<&'a Type> {
        self.this_type_index.map(|x| type_graph.type_by_index(x))
    }
    /// Returns the return value type for this function type
    pub fn return_value_type<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> &'a Type {
        type_graph.type_by_index(self.return_value_type_index)
    }
    /// Returns the argument types for this function type
    pub fn argument_types<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S) -> Vec<&'a Type> {
        self.argument_type_indices.iter().map(|x| type_graph.type_by_index(*x)).collect()
    }
    /// Returns the alignment for this function type
    pub fn size_and_alignment(&self) -> usize {
        0 // function types are sizeless
    }
}

/// Represents a single type with references to other types
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Primitive(PrimitiveType),
    Array(ArrayType),
    Pointer(PointerType),
    UDT(UserDefinedType),
    CVQualified(CVQualifiedType),
    Function(FunctionType),
}
impl Type {
    /// Returns the size of this type
    pub fn size<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        match self {
            Type::Primitive(primitive_type) => primitive_type.size_and_alignment(target_triplet),
            Type::Array(array_type) => array_type.size(type_graph, target_triplet),
            Type::Pointer(pointer_type) => pointer_type.size_and_alignment(target_triplet),
            Type::CVQualified(cv_qualified_type) => cv_qualified_type.size(type_graph, target_triplet),
            Type::Function(function_type) => function_type.size_and_alignment(),
            Type::UDT(udt_type) => udt_type.layout(type_graph, target_triplet).size,
        }
    }
    /// Returns the alignment of this type
    pub fn alignment<'a, S: TypeGraphLike<'a>>(&self, type_graph: &'a S, target_triplet: &TargetTriplet) -> usize {
        match self {
            Type::Primitive(primitive_type) => primitive_type.size_and_alignment(target_triplet),
            Type::Array(array_type) => array_type.alignment(type_graph, target_triplet),
            Type::Pointer(pointer_type) => pointer_type.size_and_alignment(target_triplet),
            Type::CVQualified(cv_qualified_type) => cv_qualified_type.alignment(type_graph, target_triplet),
            Type::Function(function_type) => function_type.size_and_alignment(),
            Type::UDT(udt_type) => udt_type.layout(type_graph, target_triplet).alignment,
        }
    }
}

/// Represents a hierarchy of a single type with references to other types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeTree {
    /// All types referenced by the root type and the root type itself
    pub types: Vec<Type>,
    /// Index of the root type this root graph represents
    pub root_type_index: usize,
}
impl TypeTree {
    /// Returns the root type of this type tree
    pub fn root_type(&self) -> &Type {
        self.type_by_index(self.root_type_index)
    }
}
impl<'a> TypeGraphLike<'a> for TypeTree {
    fn type_by_index(self: &'a Self, type_index: usize) -> &'a Type {
        &self.types[type_index]
    }
}
