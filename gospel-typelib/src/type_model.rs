use std::cell::Cell;
use std::cmp::{max, min};
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;
use anyhow::{anyhow, bail};
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use paste::paste;
use std::ptr::slice_from_raw_parts;

/// Aligns the value up to the nearest multiple of the alignment
pub fn align_value(value: usize, align: usize) -> usize {
    let reminder = if align == 0 { 0 } else { value % align };
    if reminder == 0 { value } else { value + (align - reminder) }
}

/// Describes possible endianness of the data
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DataEndianness {
    LittleEndian,
    BigEndian,
}
impl DataEndianness {
    /// Returns the endianness of the target this module has been compiled for
    pub fn host_endianness() -> DataEndianness {
        if cfg!(target_endian = "big") {
            DataEndianness::BigEndian
        } else {
            DataEndianness::LittleEndian
        }
    }
}

macro_rules! implement_integral_type_endian_conversion {
    ($data_type: ident) => {
        paste! {
            /// Converts bytes in this endian to the value of this type in endianness native for the running target
            pub fn [<$data_type _from_bytes>](self, bytes: [u8; size_of::<$data_type>()]) -> $data_type {
                match self {
                    DataEndianness::LittleEndian => $data_type::from_le_bytes(bytes),
                    DataEndianness::BigEndian => $data_type::from_be_bytes(bytes),
                }
            }
            /// Converts value of the given type in native endian to this endian
            pub fn [<$data_type _to_bytes>](self, value: $data_type) -> [u8; size_of::<$data_type>()] {
                match self {
                    DataEndianness::LittleEndian => value.to_le_bytes(),
                    DataEndianness::BigEndian => value.to_be_bytes(),
                }
            }
            /// Converts bytes in this endian to a slice of values of this type in endianness native for the running target
            pub fn [<$data_type _array_from_bytes>](self, bytes: &[u8], data: &mut [$data_type]) {
                assert_eq!(bytes.len(), data.len() * size_of::<$data_type>());
                if DataEndianness::host_endianness() == self {
                    // If endianness is the same between the host and the target, we can just transmute bytes
                    data.copy_from_slice(unsafe { &*slice_from_raw_parts(bytes.as_ptr() as *const $data_type, data.len()) })
                } else {
                    // Endianness flip is necessary
                    for data_index in 0..data.len() {
                        let start_index = data_index * size_of::<$data_type>();
                        let bytes_slice = &bytes[start_index..(start_index + size_of::<$data_type>())];
                        let mut conversion_buffer: [u8; size_of::<$data_type>()] = [0; size_of::<$data_type>()];
                        conversion_buffer.copy_from_slice(bytes_slice);
                        data[data_index] = self.[<$data_type _from_bytes>](conversion_buffer)
                    }
                }
            }
            /// Converts slice of values of the given type in native endian to this endian
            pub fn [<$data_type _array_to_bytes>](self, data: &[$data_type], bytes: &mut [u8]) {
                assert_eq!(bytes.len(), data.len() * size_of::<$data_type>());
                if DataEndianness::host_endianness() == self {
                    // If endianness is the same between the host and the target, we can just transmute bytes
                    bytes.copy_from_slice(unsafe { &*slice_from_raw_parts(data.as_ptr() as *const u8, data.len() * size_of::<$data_type>()) })
                } else {
                    // Endianness flip is necessary
                    for data_index in 0..data.len() {
                        let start_index = data_index * size_of::<$data_type>();
                        let bytes_slice = &mut bytes[start_index..(start_index + size_of::<$data_type>())];
                        bytes_slice.copy_from_slice(&self.[<$data_type _to_bytes>](data[data_index]));
                    }
                }
            }
        }
    };
}
// Utility functions for reading integral types with the explicit endianness
impl DataEndianness {
    implement_integral_type_endian_conversion!(u16);
    implement_integral_type_endian_conversion!(u32);
    implement_integral_type_endian_conversion!(u64);
    implement_integral_type_endian_conversion!(i16);
    implement_integral_type_endian_conversion!(i32);
    implement_integral_type_endian_conversion!(i64);
    implement_integral_type_endian_conversion!(f32);
    implement_integral_type_endian_conversion!(f64);
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
    Android,
}

/// Target triplet defines the target which the type layouts are being calculated for
/// This includes the operating system, the processor architecture, and environment (ABI)
/// This defines values of certain built-in input variables, as well as size of certain built-in
/// platform-dependent types such as pointer, int or long int.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub struct TargetTriplet {
    pub arch: TargetArchitecture,
    pub sys: TargetOperatingSystem,
    pub env: TargetEnvironment,
}
impl TargetTriplet {
    /// Returns the address width for the provided target triplet
    pub fn address_width(&self) -> usize {
        8 // All currently supported architectures are 64-bit
    }
    /// Returns the data endianness for the provided target triplet
    pub fn data_endianness(&self) -> DataEndianness {
        DataEndianness::LittleEndian // All currently supported architectures are Little Endian
    }
    /// Returns the size of the "long" type for the provided target triplet
    pub fn long_size(&self) -> BitWidth {
        // 4 on Win32, 8 on everything else
        if self.sys == TargetOperatingSystem::Win32 { BitWidth::Width32 } else { BitWidth::Width64 }
    }
    /// Returns the size of the "wchar_t" type for the provided target triplet
    pub fn wide_char_size(&self) -> BitWidth {
        // 2 on Win32, 4 on everything else
        if self.sys == TargetOperatingSystem::Win32 { BitWidth::Width16 } else { BitWidth::Width32 }
    }
    pub fn uses_aligned_base_class_size(&self) -> bool {
        self.env == TargetEnvironment::MSVC // MSVC uses aligned base class size when calculating layout of child class, GNU and Darwin use unaligned size
    }
    /// Returns the target that the current executable has been compiled for
    pub fn current_target() -> Option<TargetTriplet> {
        // TODO: Current implementation is not ideal, we should instead parse TARGET env var provided to us during crate compilation
        let current_arch = TargetArchitecture::current_arch();
        let current_os = TargetOperatingSystem::current_os();
        let default_env = current_os.as_ref().and_then(|x| {
            // Default environment for android OS is android, despite the OS being reported as linux (due to it being linux based)
            if std::env::consts::OS == "android" { Some(TargetEnvironment::Android) } else { x.default_env() }
        });

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

pub fn fork_type_graph<'a, T : TypeGraphLike>(graph: &'a T, type_index: usize, result: &mut TypeTree, type_lookup: &mut HashMap<usize, usize>) -> usize {
    if let Some(existing_index) = type_lookup.get(&type_index) {
        return *existing_index
    }
    // Need to add the placeholder type to reserve the slot while potentially processing subtypes
    let new_index = result.types.len();
    result.types.push(Type::Primitive(PrimitiveType::Void));
    type_lookup.insert(type_index, new_index);

    let copied_type = match graph.type_by_index(type_index) {
        Type::Pointer(pointer_type) => Type::Pointer(PointerType{pointee_type_index: fork_type_graph(graph, pointer_type.pointee_type_index, result, type_lookup), is_reference: pointer_type.is_reference}),
        Type::Array(array_type) => Type::Array(ArrayType{element_type_index: fork_type_graph(graph, array_type.element_type_index, result, type_lookup), array_length: array_type.array_length}),
        Type::CVQualified(cv_qualified_type) => Type::CVQualified(CVQualifiedType{base_type_index: fork_type_graph(graph, cv_qualified_type.base_type_index, result, type_lookup), constant: cv_qualified_type.constant, volatile: cv_qualified_type.volatile}),
        Type::Primitive(primitive_type) => Type::Primitive(primitive_type.clone()),
        Type::Function(function_type) => {
            let return_value_type_index = fork_type_graph(graph, function_type.return_value_type_index, result, type_lookup);
            let this_type_index = if let Some(value) = function_type.this_type_index { Some(fork_type_graph(graph, value, result, type_lookup)) } else { None };
            let mut argument_type_indices: Vec<usize> = Vec::new();
            for argument_type_index in &function_type.argument_type_indices {
                argument_type_indices.push(fork_type_graph(graph, *argument_type_index, result, type_lookup))
            }
            Type::Function(FunctionType{return_value_type_index, this_type_index, argument_type_indices})
        },
        Type::UDT(user_defined_type) => {
            let mut base_class_indices: Vec<usize> = Vec::new();
            for base_class_index in &user_defined_type.base_class_indices {
                base_class_indices.push(fork_type_graph(graph, *base_class_index, result, type_lookup))
            }
            let mut members: Vec<UserDefinedTypeMember> = Vec::new();
            for member in &user_defined_type.members {
                members.push(match member {
                    UserDefinedTypeMember::Field(field) => {
                        let member_type_index = fork_type_graph(graph, field.member_type_index, result, type_lookup);
                        UserDefinedTypeMember::Field(UserDefinedTypeField{name: field.name.clone(), user_alignment: field.user_alignment, member_type_index})
                    },
                    UserDefinedTypeMember::Bitfield(bitfield) => UserDefinedTypeMember::Bitfield(bitfield.clone()),
                    UserDefinedTypeMember::VirtualFunction(function_declaration) => {
                        let return_value_type_index = fork_type_graph(graph, function_declaration.return_value_type_index, result, type_lookup);
                        let mut parameters: Vec<FunctionParameterDeclaration> = Vec::new();
                        for function_parameter in &function_declaration.parameters {
                            let parameter_type_index = fork_type_graph(graph, function_parameter.parameter_type_index, result, type_lookup);
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
        Type::Enum(enum_type) => Type::Enum(enum_type.clone()),
    };
    result.types[new_index] = copied_type;
    new_index
}

/// Common trait for all type graph-like structs
pub trait TypeGraphLike {
    /// Returns the type at the specified index in the type graph
    fn type_by_index(&self, type_index: usize) -> &Type;

    /// Creates an isolated type tree describing the type at the given index and its dependencies
    fn type_tree(&self, type_index: usize) -> TypeTree where Self: Sized {
        let mut result = TypeTree{types: Vec::new(), root_type_index: 0};
        let mut type_lookup: HashMap<usize, usize> = HashMap::new();
        let root_type_index = fork_type_graph(self, type_index, &mut result, &mut type_lookup);
        result.root_type_index = root_type_index;
        result
    }
    fn base_type_index(&self, type_index: usize) -> usize {
        let type_data = self.type_by_index(type_index);
        if let Type::CVQualified(cv_qualified_type) = type_data {
            self.base_type_index(cv_qualified_type.base_type_index)
        } else { type_index }
    }
    /// Returns base type corresponding to the type at the specified index. Will unwrap CV-qualified type to the underlying type
    fn base_type_by_index(&self, type_index: usize) -> &Type {
        self.type_by_index(self.base_type_index(type_index))
    }
    fn cv_qualified_type_at_index(&self, type_index: usize) -> Option<CVQualifiedType> {
        let type_data = self.type_by_index(type_index);
        if let Type::CVQualified(cv_qualified_type) = type_data {
            Some(cv_qualified_type.clone())
        } else { None }
    }
}

/// Represents an argument provided to the template to be constructed into a named type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeTemplateArgument {
    Type(usize),
    Integer(u64),
}

/// Trait for type graph structures that can be mutated
pub trait MutableTypeGraph : TypeGraphLike {
    /// Adds type to the type graph and returns its index. If this type is already part of the type graph, returns index of an existing type
    fn store_type(&mut self, type_data: Type) -> usize;
    /// Attempts to find or create UDT type by its qualified name (with $ as a separator and : used to separate module name from local type name. Resulting format is module:namespace$typename)
    fn create_named_type(&mut self, full_type_name: &str, arguments: Vec<TypeTemplateArgument>) -> anyhow::Result<Option<usize>>;
}

/// Type layout cache caches type layout calculations for arbitrary types
#[derive(Debug, Clone)]
pub struct TypeLayoutCache {
    pub target_triplet: TargetTriplet,
    type_cache: HashMap<usize, (usize, usize)>,
    udt_cache: HashMap<usize, Arc<ResolvedUDTLayout>>,
}
impl TypeLayoutCache {
    /// Creates a new type layout cache for the given target triplet
    pub fn create(target_triplet: TargetTriplet) -> Self {
        Self{target_triplet, type_cache: HashMap::new(), udt_cache: HashMap::new()}
    }
}

/// Calculates the offset that needs to be applied to the pointer to from_type_index to convert it to a pointer to to_type_index. Returns None if pointee types are incompatible and conversion is not possible
pub fn calculate_static_cast_pointer_adjust(type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache, from_type_index: usize, to_type_index: usize) -> Option<i64> {
    let from_base_type_index = type_graph.base_type_index(from_type_index);
    let to_base_type_index = type_graph.base_type_index(to_type_index);
    let from_base_type = type_graph.type_by_index(from_base_type_index);
    let to_base_type = type_graph.type_by_index(to_base_type_index);

    if from_base_type_index == to_base_type_index {
        // Shortcut for when from and to is the same base type
        Some(0)
    } else if let Type::Primitive(from_primitive_type) = from_base_type && let Type::Primitive(to_primitive_type) = to_base_type {
        // Primitive types can only be converted in-place, so their offset is always 0
        if are_primitive_types_convertible(*from_primitive_type, *to_primitive_type, &layout_cache.target_triplet) { Some(0) } else { None }
    } else if let Type::Enum(from_enum_type) = from_base_type && let Type::Primitive(to_primitive_type) = to_base_type {
        // Enum type can be converted to primitive type if its underlying type can be converted to it
        let from_underlying_type = from_enum_type.underlying_type(&layout_cache.target_triplet).unwrap();
        if are_primitive_types_convertible(from_underlying_type, *to_primitive_type, &layout_cache.target_triplet) { Some(0) } else { None }
    } else if let Type::Primitive(from_primitive_type) = from_base_type && let Type::Enum(to_enum_type) = to_base_type {
        // Primitive type can be converted to enum type if it can be converted to its underlying type
        let to_underlying_type = to_enum_type.underlying_type(&layout_cache.target_triplet).unwrap();
        if are_primitive_types_convertible(*from_primitive_type, to_underlying_type, &layout_cache.target_triplet) { Some(0) } else { None }
    } else if let Type::Pointer(from_pointer_type) = from_base_type && let Type::Pointer(to_pointer_type) = to_base_type {
        // Pointer types are only convertible if pointee type can be converted without applying any adjustment
        // Re-entry to get_static_cast_pointer_adjust is okay in this context because read lock that we are holding can be shared
        if calculate_static_cast_pointer_adjust(type_graph, layout_cache, from_pointer_type.pointee_type_index, to_pointer_type.pointee_type_index) == Some(0) { Some(0) } else { None }
    } else if let Type::Array(from_array_type) = from_base_type && let Type::Array(to_array_type) = to_base_type {
        // Similar logic applies to arrays as it does to pointers, two array types are convertible if their element types are convertible without any adjustment
        // Arrays also have an additional requirement of their length being equal
        if from_array_type.array_length == to_array_type.array_length &&
            calculate_static_cast_pointer_adjust(type_graph, layout_cache, from_array_type.element_type_index, to_array_type.element_type_index) == Some(0) { Some(0) } else { None }
    } else if let Type::UDT(from_user_defined_type) = from_base_type && let Type::UDT(to_user_defined_type) = to_base_type {
        // Struct types can be upcast or downcast. Try upcasting (casting from derived class to base class first) first, and then downcasting (casting from base class to derived class) as a fallback
        let base_class_offsets= from_user_defined_type.find_all_base_class_offsets(from_base_type_index, to_base_type_index, type_graph, layout_cache).unwrap();
        if  !base_class_offsets.is_empty() {
            // When upcasting, base class is located at positive offset from this pointer. In this case, it is also safe to pick any instance of base class within the derived class, preferring for the outermost first instance
            Some(base_class_offsets[0] as i64)
        } else if let derived_class_offsets = to_user_defined_type.find_all_base_class_offsets(to_base_type_index, from_base_type_index, type_graph, layout_cache).unwrap() && derived_class_offsets.len() == 1 {
            // Downcasting can only be performed where there is only once instance of base class in the hierarchy chain. When there are multiple instances, it is not possible to know pointer to which instance we have
            // Downcasting also goes from base to derived class, which is at lower addresses, so the offset here is negative
            Some(-(derived_class_offsets[0] as i64))
        } else {
            // Given UDTs are not related otherwise, and the cast is not possible
            None
        }
    } else if let Type::Primitive(to_primitive_type) = to_base_type && to_primitive_type == &PrimitiveType::Void {
        // Anything can be cast to void type without pointer adjust
        Some(0)
    } else {
        // Types are not related otherwise and there is no implicit conversion available
        None
    }
}

fn are_primitive_types_convertible(from_primitive_type: PrimitiveType, to_primitive_type: PrimitiveType, target_triplet: &TargetTriplet) -> bool {
    // Primitive types are convertible if they are of the same bit width and integral status. Signedness changing conversions are allowed
    if let Some(from_bit_width) = from_primitive_type.bit_width(&target_triplet) &&
        let Some(to_bit_width) = to_primitive_type.bit_width(&target_triplet) &&
        from_bit_width == to_bit_width && from_primitive_type.is_integral() == to_primitive_type.is_integral() {
        return true;
    }
    // Otherwise, primitive types are convertible if they are the exact same type, or to type is void
    if from_primitive_type == to_primitive_type || to_primitive_type == PrimitiveType::Void {
        return true;
    }
    false
}

/// Represents possible bit width values for integral types
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Display, EnumString)]
pub enum BitWidth {
    Width8,
    Width16,
    Width32,
    Width64,
}
impl BitWidth {
    /// Returns bit width value in bytes
    pub fn value_in_bytes(self) -> usize {
        match self {
            BitWidth::Width8 => 1,
            BitWidth::Width16 => 2,
            BitWidth::Width32 => 4,
            BitWidth::Width64 => 8,
        }
    }
}

/// Describes whenever an integral type is signed or unsigned
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Display, EnumString)]
pub enum IntegerSignedness {
    Signed,
    Unsigned,
}

/// Describes an integral type of given bit width and signedness
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct IntegralType {
    pub bit_width: BitWidth,
    pub signedness: IntegerSignedness,
}
impl Default for IntegralType {
    fn default() -> Self {
        Self{bit_width: BitWidth::Width32, signedness: IntegerSignedness::Signed}
    }
}

macro_rules! implement_integer_cast_block {
    ($value:expr, $to_type:expr, $source_type:ty) => {
        match $to_type.bit_width {
            BitWidth::Width8 =>  $value as $source_type as u8  as u64,
            BitWidth::Width16 => $value as $source_type as u16 as u64,
            BitWidth::Width32 => $value as $source_type as u32 as u64,
            BitWidth::Width64 => $value as $source_type as u64 as u64,
        }
    };
}
macro_rules! implement_integer_fit_check_block {
    ($value:expr, $fit_check_type:expr, $source_type:ty) => {
        match $fit_check_type.signedness {
            IntegerSignedness::Signed => match $fit_check_type.bit_width {
                BitWidth::Width8 =>  (($value as $source_type) >= 0 || ($value as $source_type as i64) >= i8::MIN  as i64) && ($value as $source_type as u64) <= i8::MAX  as u64,
                BitWidth::Width16 => (($value as $source_type) >= 0 || ($value as $source_type as i64) >= i16::MIN as i64) && ($value as $source_type as u64) <= i16::MAX as u64,
                BitWidth::Width32 => (($value as $source_type) >= 0 || ($value as $source_type as i64) >= i32::MIN as i64) && ($value as $source_type as u64) <= i32::MAX as u64,
                BitWidth::Width64 => (($value as $source_type) >= 0 || ($value as $source_type as i64) >= i64::MIN as i64) && ($value as $source_type as u64) <= i64::MAX as u64,
            },
            IntegerSignedness::Unsigned => match $fit_check_type.bit_width {
                BitWidth::Width8 =>  ($value as $source_type) >= 0 && ($value as $source_type as u64) <= u8::MAX  as u64,
                BitWidth::Width16 => ($value as $source_type) >= 0 && ($value as $source_type as u64) <= u16::MAX as u64,
                BitWidth::Width32 => ($value as $source_type) >= 0 && ($value as $source_type as u64) <= u32::MAX as u64,
                BitWidth::Width64 => ($value as $source_type) >= 0 && ($value as $source_type as u64) <= u64::MAX as u64,
            },
        }
    };
}
#[macro_export]
macro_rules! map_integral_value {
    ($value_type:expr, $raw_value:expr, |$converted_value:ident| $expression:expr, signed) => {
        match $value_type.bit_width {
            BitWidth::Width8 =>  { let $converted_value = $raw_value as i8 ; let result: i8  = $expression; result as u64 },
            BitWidth::Width16 => { let $converted_value = $raw_value as i16; let result: i16 = $expression; result as u64 },
            BitWidth::Width32 => { let $converted_value = $raw_value as i32; let result: i32 = $expression; result as u64 },
            BitWidth::Width64 => { let $converted_value = $raw_value as i64; let result: i64 = $expression; result as u64 },
        }
    };
    ($value_type:expr, $raw_value:expr, |$converted_value:ident| $expression:expr, unsigned) => {
        match $value_type.bit_width {
            BitWidth::Width8 =>  { let $converted_value = $raw_value as u8 ; let result: u8  = $expression; result as u64 },
            BitWidth::Width16 => { let $converted_value = $raw_value as u16; let result: u16 = $expression; result as u64 },
            BitWidth::Width32 => { let $converted_value = $raw_value as u32; let result: u32 = $expression; result as u64 },
            BitWidth::Width64 => { let $converted_value = $raw_value as u64; let result: u64 = $expression; result as u64 },
        }
    };
    ($value_type:expr, $raw_value:expr, |$converted_value:ident| $expression:expr, mixed) => {
        match $value_type.signedness {
            IntegerSignedness::Signed =>   map_integral_value!($value_type, $raw_value, |$converted_value| $expression, signed  ),
            IntegerSignedness::Unsigned => map_integral_value!($value_type, $raw_value, |$converted_value| $expression, unsigned),
        }
    };
    ($value_type:expr, $raw_value_a:expr, $raw_value_b:expr, |$converted_value_a:ident, $converted_value_b:ident| $expression:expr, signed) => {
        match $value_type.bit_width {
            BitWidth::Width8 =>  { let $converted_value_a = $raw_value_a as i8 ; let $converted_value_b = $raw_value_b as i8 ; let result: i8  = $expression; result as u64 },
            BitWidth::Width16 => { let $converted_value_a = $raw_value_a as i16; let $converted_value_b = $raw_value_b as i16; let result: i16 = $expression; result as u64 },
            BitWidth::Width32 => { let $converted_value_a = $raw_value_a as i32; let $converted_value_b = $raw_value_b as i32; let result: i32 = $expression; result as u64 },
            BitWidth::Width64 => { let $converted_value_a = $raw_value_a as i64; let $converted_value_b = $raw_value_b as i64; let result: i64 = $expression; result as u64 },
        }
    };
    ($value_type:expr, $raw_value_a:expr, $raw_value_b:expr, |$converted_value_a:ident, $converted_value_b:ident| $expression:expr, unsigned) => {
        match $value_type.bit_width {
            BitWidth::Width8 =>  { let $converted_value_a = $raw_value_a as u8 ; let $converted_value_b = $raw_value_b as u8 ; let result: u8  = $expression; result as u64 },
            BitWidth::Width16 => { let $converted_value_a = $raw_value_a as u16; let $converted_value_b = $raw_value_b as u16; let result: u16 = $expression; result as u64 },
            BitWidth::Width32 => { let $converted_value_a = $raw_value_a as u32; let $converted_value_b = $raw_value_b as u32; let result: u32 = $expression; result as u64 },
            BitWidth::Width64 => { let $converted_value_a = $raw_value_a as u64; let $converted_value_b = $raw_value_b as u64; let result: u64 = $expression; result as u64 },
        }
    };
    ($value_type:expr, $raw_value_a:expr, $raw_value_b:expr, |$converted_value_a:ident, $converted_value_b:ident| $expression:expr, mixed) => {
        match $value_type.signedness {
            IntegerSignedness::Signed =>   map_integral_value!($value_type, $raw_value_a, $raw_value_b, |$converted_value_a, $converted_value_b| $expression, signed  ),
            IntegerSignedness::Unsigned => map_integral_value!($value_type, $raw_value_a, $raw_value_b, |$converted_value_a, $converted_value_b| $expression, unsigned),
        }
    };
}
impl IntegralType {
    /// Casts integer value from one integral type to another integral type
    /// This follows rust native cast semantics:
    /// - casting from larger type to a smaller type results in truncation (regardless of signedness of either operand)
    /// - casting from smaller signed type to larger type results in sign extension
    /// - casting from smaller unsigned type to larger type results in zero extension
    #[allow(clippy::unnecessary_cast)]
    pub fn cast_integral_value(value: u64, from_type: &IntegralType, to_type: &IntegralType) -> u64 {
        match from_type.signedness {
            IntegerSignedness::Signed => match from_type.bit_width {
                BitWidth::Width8  => implement_integer_cast_block!(value, to_type, i8 ),
                BitWidth::Width16 => implement_integer_cast_block!(value, to_type, i16),
                BitWidth::Width32 => implement_integer_cast_block!(value, to_type, i32),
                BitWidth::Width64 => implement_integer_cast_block!(value, to_type, i64),
            },
            IntegerSignedness::Unsigned => match from_type.bit_width {
                BitWidth::Width8  => implement_integer_cast_block!(value, to_type, u8 ),
                BitWidth::Width16 => implement_integer_cast_block!(value, to_type, u16),
                BitWidth::Width32 => implement_integer_cast_block!(value, to_type, u32),
                BitWidth::Width64 => implement_integer_cast_block!(value, to_type, u64),
            }
        }
    }
    /// Returns true if the given integral value fits within the given integral type range
    #[allow(unused_comparisons)]
    #[allow(clippy::unnecessary_cast)]
    pub fn can_fit_integral_value(value: u64, value_type: &IntegralType, check_fit_type: &IntegralType) -> bool {
        match value_type.signedness {
            IntegerSignedness::Signed => match value_type.bit_width {
                BitWidth::Width8  => implement_integer_fit_check_block!(value, check_fit_type, i8 ),
                BitWidth::Width16 => implement_integer_fit_check_block!(value, check_fit_type, i16),
                BitWidth::Width32 => implement_integer_fit_check_block!(value, check_fit_type, i32),
                BitWidth::Width64 => implement_integer_fit_check_block!(value, check_fit_type, i64),
            },
            IntegerSignedness::Unsigned => match value_type.bit_width {
                BitWidth::Width8  => implement_integer_fit_check_block!(value, check_fit_type, u8 ),
                BitWidth::Width16 => implement_integer_fit_check_block!(value, check_fit_type, u16),
                BitWidth::Width32 => implement_integer_fit_check_block!(value, check_fit_type, u32),
                BitWidth::Width64 => implement_integer_fit_check_block!(value, check_fit_type, u64),
            }
        }
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
    /// Returns true if this primitive type is sizeless
    pub fn is_sizeless(self) -> bool {
        self == PrimitiveType::Void
    }
    /// Returns true if this primitive type is floating point
    pub fn is_floating_point(self) -> bool {
        self == PrimitiveType::Float || self == PrimitiveType::Double
    }
    /// Returns true if this primitive type is integral. All primitive types except for float, double and void are integral
    pub fn is_integral(self) -> bool {
        self.integer_signedness().is_some()
    }
    /// Returns the sign of this type if this type is an integral type. This will return None for floating point and non-integral types
    pub fn integer_signedness(self) -> Option<IntegerSignedness> {
        match self {
            PrimitiveType::Char => Some(IntegerSignedness::Signed),
            PrimitiveType::UnsignedChar => Some(IntegerSignedness::Unsigned),
            PrimitiveType::WideChar => Some(IntegerSignedness::Unsigned),
            PrimitiveType::ShortInt => Some(IntegerSignedness::Signed),
            PrimitiveType::UnsignedShortInt => Some(IntegerSignedness::Unsigned),
            PrimitiveType::Int => Some(IntegerSignedness::Signed),
            PrimitiveType::UnsignedInt => Some(IntegerSignedness::Unsigned),
            PrimitiveType::Bool => Some(IntegerSignedness::Unsigned),
            PrimitiveType::LongInt => Some(IntegerSignedness::Signed),
            PrimitiveType::UnsignedLongInt => Some(IntegerSignedness::Unsigned),
            PrimitiveType::LongLongInt => Some(IntegerSignedness::Signed),
            PrimitiveType::UnsignedLongLongInt => Some(IntegerSignedness::Unsigned),
            PrimitiveType::Char8 => Some(IntegerSignedness::Unsigned),
            PrimitiveType::Char16 => Some(IntegerSignedness::Unsigned),
            PrimitiveType::Char32 => Some(IntegerSignedness::Unsigned),
            _ => None
        }
    }
    /// Returns the bit width of this type. Will return None for sizeless types (e.g. void)
    pub fn bit_width(self, target_triplet: &TargetTriplet) -> Option<BitWidth> {
        match self {
            PrimitiveType::Void => None,
            PrimitiveType::Char => Some(BitWidth::Width8),
            PrimitiveType::UnsignedChar => Some(BitWidth::Width8),
            PrimitiveType::WideChar => Some(target_triplet.wide_char_size()),
            PrimitiveType::ShortInt => Some(BitWidth::Width16),
            PrimitiveType::UnsignedShortInt => Some(BitWidth::Width16),
            PrimitiveType::Int => Some(BitWidth::Width32),
            PrimitiveType::UnsignedInt => Some(BitWidth::Width32),
            PrimitiveType::Float => Some(BitWidth::Width32),
            PrimitiveType::Double => Some(BitWidth::Width64),
            PrimitiveType::Bool => Some(BitWidth::Width8),
            PrimitiveType::LongInt => Some(target_triplet.long_size()),
            PrimitiveType::UnsignedLongInt => Some(target_triplet.long_size()),
            PrimitiveType::LongLongInt => Some(BitWidth::Width64),
            PrimitiveType::UnsignedLongLongInt => Some(BitWidth::Width64),
            PrimitiveType::Char8 => Some(BitWidth::Width8),
            PrimitiveType::Char16 => Some(BitWidth::Width16),
            PrimitiveType::Char32 => Some(BitWidth::Width32),
        }
    }
    /// Converts this primitive type to integral type value with resolved bit width and signedness for the given target triplet. Returns None if type is not an integral type
    pub fn to_integral_type(self, target_triplet: &TargetTriplet) -> Option<IntegralType> {
        let bit_width = self.bit_width(target_triplet)?;
        let signedness = self.integer_signedness()?;
        Some(IntegralType{bit_width, signedness})
    }
    /// Returns the size and the alignment of this type for the given target triplet
    pub fn size_and_alignment(self, target_triplet: &TargetTriplet) -> anyhow::Result<usize> {
        Ok(self.bit_width(target_triplet).ok_or_else(|| anyhow!("Void type is sizeless"))?.value_in_bytes())
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
    pub fn element_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> &'a Type {
        type_graph.type_by_index(self.element_type_index)
    }
    /// Returns the size and alignment of the array type
    pub fn size_and_alignment<'a>(&self, type_graph: &'a dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<(usize, usize)> {
        let (element_size, element_alignment) = Type::size_and_alignment(self.element_type_index, type_graph, layout_cache)?;
        Ok((element_size * self.array_length, element_alignment))
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
    pub fn pointee_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> &'a Type {
        type_graph.type_by_index(self.pointee_type_index)
    }
    /// Returns the size and alignment of the pointer type
    pub fn size_and_alignment(&self, target_triplet: &TargetTriplet) -> usize {
        target_triplet.address_width()
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
    pub fn member_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> &'a Type {
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
pub struct MemberLayoutMapContext<'a, 'b> {
    pub owner_udt: &'a UserDefinedType,
    pub owner_layout: &'b Arc<ResolvedUDTLayout>,
    pub owner_offset: usize,
    pub member_index: usize,
}
impl UserDefinedType {

    /// Returns true if this user defined type is a child of the given base class (this will not check if this is the same type!)
    pub fn is_child_of(&self, base_class_index: usize, type_graph: &dyn TypeGraphLike) -> bool {
        self.base_class_indices.contains(&base_class_index) || self.base_class_indices.iter()
            .filter_map(|x| if let Type::UDT(y) = type_graph.type_by_index(*x) { Some(y) } else { None })
            .any(|x| x.is_child_of(base_class_index, type_graph))
    }
    /// Returns recursive iterator over base classes. Note that this can return the same base class multiple types
    pub fn base_class_recursive_iterator(&self, type_graph: &dyn TypeGraphLike) -> impl Iterator<Item = usize> {
        self.base_class_indices.iter().cloned().chain(self.base_class_indices.iter()
            .filter_map(|x| if let Type::UDT(y) = type_graph.type_by_index(*x) { Some(y) } else { None })
            .flat_map(|x| x.base_class_recursive_iterator(type_graph))
            .collect::<Vec<usize>>())
    }
    /// Attempts to find a member with the given name in this class or base classes, and returns the first member found
    pub fn find_map_member_by_name<T, S: Fn(&UserDefinedTypeMember) -> Option<T>>(&self, name: &str, mapper: &S, type_graph: &dyn TypeGraphLike) -> Option<T> {
        if let Some(direct_member) = self.members.iter().find_map(|x| if x.name() == Some(name) && let Some(mapped_value) = mapper(x) { Some(mapped_value) } else { None }) {
            Some(direct_member)
        } else {
            self.base_class_indices.iter()
                .filter_map(|x| if let Type::UDT(y) = type_graph.type_by_index(*x) { Some(y) } else { None })
                .find_map(|x| x.find_map_member_by_name(name, mapper, type_graph))
        }
    }
    /// Resolved the layout of this user defined type for a particular target triplet
    pub fn layout(&self, type_index: usize, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<Arc<ResolvedUDTLayout>> {
        if let Some(existing_layout) = layout_cache.udt_cache.get(&type_index) {
            return Ok(existing_layout.clone());
        }
        let new_layout = Arc::new(self.calculate_layout_internal(type_graph, layout_cache)?);
        layout_cache.udt_cache.insert(type_index, new_layout.clone());
        Ok(new_layout)
    }
    /// Returns size and alignment of this user defined type
    pub fn size_and_alignment(&self, type_index: usize, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<(usize, usize)> {
        let layout = self.layout(type_index, type_graph, layout_cache)?;
        Ok((layout.size, layout.alignment))
    }
    /// Returns all offsets of the given base class from the start of the user defined type. Can return multiple results if the same base class appears multiple times at different levels in the class hierarchy
    pub fn find_all_base_class_offsets(&self, type_index: usize, base_class_index: usize, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<Vec<usize>> {
        let type_layout = self.layout(type_index, type_graph, layout_cache)?;
        let mut all_base_class_offsets: Vec<usize> = Vec::new();
        // Try direct base classes first (in case of the same base class being present multiple times at different levels of class hierarchy)
        for i in 0..self.base_class_indices.len() {
            if self.base_class_indices[i] == base_class_index {
                all_base_class_offsets.push(type_layout.base_class_offsets[i]);
            }
        }
        // Try to recursively look up base classes of our base classes now
        for i in 0..self.base_class_indices.len() {
            if let Type::UDT(base_class_udt) = type_graph.type_by_index(self.base_class_indices[i]) {
                all_base_class_offsets.extend(base_class_udt.find_all_base_class_offsets(self.base_class_indices[i], base_class_index, type_graph, layout_cache)?.into_iter()
                    .map(|base_class_relative_offset| type_layout.base_class_offsets[i] + base_class_relative_offset));
            }
        }
        // Did not find the base class in our class hierarchy
        Ok(all_base_class_offsets)
    }
    /// Attempts to find a member by name in this user defined type or its base class, and runs the map function on it
    pub fn find_map_member_layout<T, S: Fn(&MemberLayoutMapContext) -> Option<T>>(&self, type_index: usize, name: &str, map_function: &S, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<Option<T>> {
        self.find_map_member_layout_internal(type_index, name, map_function, 0, type_graph, layout_cache)
    }
    fn find_map_member_layout_internal<T, S: Fn(&MemberLayoutMapContext) -> Option<T>>(&self, type_index: usize, name: &str, map_function: &S, base_offset: usize, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<Option<T>> {
        let type_layout = self.layout(type_index, type_graph, layout_cache)?;

        // Check members of this user defined type before checking base classes
        for i in 0..self.members.len() {
            if self.members[i].name() == Some(name) && let Some(result) = map_function(&MemberLayoutMapContext{owner_offset: base_offset, owner_udt: self, owner_layout: &type_layout, member_index: i}) {
                return Ok(Some(result));
            }
        }
        // Base class members are used as a fallback
        for i in 0..self.base_class_indices.len() {
            if let Type::UDT(base_class) = type_graph.type_by_index(self.base_class_indices[i]) &&
                let Some(result) = base_class.find_map_member_layout_internal(type_index, name, map_function, base_offset + type_layout.base_class_offsets[i], type_graph, layout_cache)? {
                return Ok(Some(result))
            }
        }
        // Did not find member with the given name in this class or any base classes
        Ok(None)
    }
    fn calculate_layout_internal<'a>(&self, type_graph: &'a dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<ResolvedUDTLayout> {
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

        let base_class_layouts: Vec<Arc<ResolvedUDTLayout>> = self.base_class_indices.iter()
            .map(|x| (x, type_graph.type_by_index(*x)))
            .filter_map(|(index, type_ref)| if let Type::UDT(base_class) = type_ref { Some((index, base_class)) } else { None })
            .map(|(base_class_index, base_class_type)| base_class_type.layout(*base_class_index, type_graph, layout_cache).map_err(|error| {
                let base_class_name = base_class_type.name.as_ref().map(|x| x.as_str()).unwrap_or("<unnamed type>");
                anyhow!("Failed to calculate layout of base class {}: {}", base_class_name, error)
            }))
            .collect::<anyhow::Result<Vec<Arc<ResolvedUDTLayout>>>>()?;

        if self.kind != UserDefinedTypeKind::Union {
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
                    let size_and_alignment = layout_cache.target_triplet.address_width();
                    vtable_function_start_offset = calculate_member_offset(size_and_alignment, size_and_alignment);
                    let slot_size = layout_cache.target_triplet.address_width();
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
                let base_class_size = if layout_cache.target_triplet.uses_aligned_base_class_size() { base_class.size } else { base_class.unaligned_size };

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
        } else if !base_class_layouts.is_empty() {
            bail!("Union types cannot have base classes");
        }

        // Layout fields in memory sequentially or in parallel, merging multiple bitfields into the single field when possible
        let mut member_layouts: Vec<ResolvedUDTMemberLayout> = Vec::with_capacity(self.members.len());
        let mut current_unique_virtual_function_index: usize = 0;

        for member_index in 0..self.members.len() {
            let member = &self.members[member_index];

            if let UserDefinedTypeMember::VirtualFunction(virtual_function) = member {
                if self.kind != UserDefinedTypeKind::Union {
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
                        bail!("Base function for virtual function override {} does not exist", virtual_function.name);
                    }
                } else {
                    bail!("Union types cannot have virtual functions");
                }
            } else if let UserDefinedTypeMember::Field(field) = member {
                let (member_size, member_type_alignment) = Type::size_and_alignment(field.member_type_index, type_graph, layout_cache)
                    .map_err(|error| {
                        let member_name = member.name().unwrap_or("<unnamed member>");
                        anyhow!("Failed to calculate member {} size: {}", member_name, error)
                    })?;
                let member_alignment = max(1, max(member_type_alignment, field.user_alignment.unwrap_or(0)));

                let member_offset = calculate_member_offset(member_size, member_alignment);
                let result_layout = ResolvedUDTFieldLayout{ offset: member_offset, alignment: member_alignment, size: member_size };
                member_layouts.push(ResolvedUDTMemberLayout::Field(result_layout));

            } else if let UserDefinedTypeMember::Bitfield(bitfield) = member {
                // If this is a bitfield, and the previous member has the same type and alignment as this one, and is also a bitfield, and has enough space to fit this bitfield in it,
                // copy the offset and other data from the previous field but update the bitfield location to point to this bitfield
                let maximum_bitfield_width = bitfield.primitive_type.size_and_alignment(&layout_cache.target_triplet)? * 8;
                if member_index > 0 &&
                    let ResolvedUDTMemberLayout::Bitfield(previous_bitfield) = &member_layouts[member_index - 1] &&
                    let bitfield_start_offset = previous_bitfield.bitfield_offset + previous_bitfield.bitfield_width &&
                    (bitfield_start_offset + bitfield.bitfield_width) <= maximum_bitfield_width {

                    let result_layout = ResolvedUDTBitfieldLayout{ offset: previous_bitfield.offset, size: previous_bitfield.size, bitfield_offset: bitfield_start_offset, bitfield_width: bitfield.bitfield_width };
                    member_layouts.push(ResolvedUDTMemberLayout::Bitfield(result_layout));
                } else {
                    let member_size_and_alignment = bitfield.primitive_type.size_and_alignment(&layout_cache.target_triplet)?;

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
        Ok(ResolvedUDTLayout{alignment: current_alignment.get(), unaligned_size, size: current_size.get(), vtable: vtable_layout, virtual_function_lookup, base_class_offsets, member_layouts})
    }
}

/// Represents a kind of enum
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize, Display, EnumString)]
pub enum EnumKind {
    /// enum
    #[default]
    Unscoped,
    /// enum class
    Scoped,
}

/// Represents a constant defined within the enumeration
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct EnumConstant {
    /// Name of the enum constant
    pub name: Option<String>,
    /// Raw value of the enum constant. Note that this is zero-extended to 64 bits, even for signed values, never sign-extended
    /// This value is also not validated against the underlying type and can be different from the actual value in case of implicit narrowing occuring
    /// For actual value, use EnumType.constant_value
    pub raw_value: u64,
    /// Integral type of this enum constant
    pub integral_type: IntegralType,
}

/// Represents an enumeration type (enum or enum class)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct EnumType {
    /// Type of the enum (scoped vs unscoped)
    pub kind: EnumKind,
    /// Name of this enum type
    pub name: Option<String>,
    /// Primitive type for this enumeration, if specified. This must be an integral type
    pub underlying_type: Option<PrimitiveType>,
    /// All constants defined as a part of this enum
    pub constants: Vec<EnumConstant>,
}
impl EnumType {
    /// Calculates the underlying type for the enum type if it can be known without target triplet and full constant value set
    pub fn underlying_type_no_target_no_constants(&self) -> Option<PrimitiveType> {
        if let Some(explicit_underlying_type) = self.underlying_type {
            return Some(explicit_underlying_type);
        }
        // Scoped enums always use Int as their underlying type
        if self.kind == EnumKind::Scoped {
            Some(PrimitiveType::Int)
        } else { None }
    }
    /// Returns the default integral type for the constant given the target triplet
    pub fn default_constant_integral_type(&self, target_triplet: &TargetTriplet) -> anyhow::Result<IntegralType> {
        // default type for unscoped enumerations is int on MSVC and unsigned int for everything else
        let underlying_type = self.underlying_type_no_target_no_constants()
            .unwrap_or(if target_triplet.env == TargetEnvironment::MSVC { PrimitiveType::Int } else { PrimitiveType::UnsignedInt });
        underlying_type.to_integral_type(target_triplet)
            .ok_or_else(|| anyhow!("Underlying enum type {} is not an integral type", underlying_type))
    }
    /// Calculates the underlying type for the enum type. This relies on platform specific logic for unscoped enums
    pub fn underlying_type(&self, target_triplet: &TargetTriplet) -> anyhow::Result<PrimitiveType> {
        if let Some(explicit_underlying_type) = self.underlying_type {
            return Ok(explicit_underlying_type);
        }
        // Scoped enums and all unscoped enums under MSVC always use Int as their underlying type
        if self.kind == EnumKind::Scoped || target_triplet.env == TargetEnvironment::MSVC {
            return Ok(PrimitiveType::Int);
        }
        // Unscoped enums under gnu convention pick int if all values (ignoring their types) fit within 32 bits, and long int if there are 64-bit values.
        // Unsigned types are picked if there are no signed constants with values below 0
        let mut can_fit_within_i32 = false;
        let mut can_fit_within_u32 = false;
        let mut can_fit_within_i64 = false;
        let mut can_fit_within_u64 = false;

        for constant in &self.constants {
            can_fit_within_i32 |= IntegralType::can_fit_integral_value(constant.raw_value, &constant.integral_type, &IntegralType{bit_width: BitWidth::Width32, signedness: IntegerSignedness::Signed});
            can_fit_within_u32 |= IntegralType::can_fit_integral_value(constant.raw_value, &constant.integral_type, &IntegralType{bit_width: BitWidth::Width32, signedness: IntegerSignedness::Unsigned});
            can_fit_within_i64 |= IntegralType::can_fit_integral_value(constant.raw_value, &constant.integral_type, &IntegralType{bit_width: BitWidth::Width64, signedness: IntegerSignedness::Signed});
            can_fit_within_u64 |= IntegralType::can_fit_integral_value(constant.raw_value, &constant.integral_type, &IntegralType{bit_width: BitWidth::Width64, signedness: IntegerSignedness::Unsigned});
        }
        if can_fit_within_u32 {
            Ok(PrimitiveType::UnsignedInt)
        } else if can_fit_within_i32 {
            Ok(PrimitiveType::Int)
        } else if can_fit_within_u64 {
            Ok(PrimitiveType::UnsignedLongInt)
        } else if can_fit_within_i64 {
            Ok(PrimitiveType::LongInt)
        } else {
            Err(anyhow!("Cannot find an integral type capable of storing values of all constants"))
        }
    }
    /// Returns the size and alignment of this enum type
    pub fn size_and_alignment(&self, target_triplet: &TargetTriplet) -> anyhow::Result<(usize, usize)> {
        let size_and_alignment = self.underlying_type(target_triplet)?.size_and_alignment(target_triplet)?;
        Ok((size_and_alignment, size_and_alignment))
    }
    /// Calculates the value of the constant using the underlying type of the enum for the given target triplet
    pub fn constant_value(&self, constant: &EnumConstant, target_triplet: &TargetTriplet) -> anyhow::Result<u64> {
        let underlying_type = self.underlying_type(target_triplet)?;
        let underlying_integral_type = underlying_type.to_integral_type(target_triplet)
            .ok_or_else(|| anyhow!("Underlying enum type {} is not an integral type", underlying_type))?;

        // Non-MSVC targets actually make sure that no data is lost and no signed negative value to unsigned value conversion occurs
        // MSVC just implicitly performs narrowing conversion and signed-to-unsigned conversion
        if target_triplet.env != TargetEnvironment::MSVC {
            if !IntegralType::can_fit_integral_value(constant.raw_value, &constant.integral_type, &underlying_integral_type) {
                bail!("Constant value of of range of underlying enumeration type");
            }
        }
        Ok(IntegralType::cast_integral_value(constant.raw_value, &constant.integral_type, &underlying_integral_type))
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
    pub fn base_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> &'a Type {
        type_graph.type_by_index(self.base_type_index)
    }
    /// Returns the size and alignment of this CV-qualified type
    pub fn size_and_alignment<'a>(&self, type_graph: &'a dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<(usize, usize)> {
        Type::size_and_alignment(self.base_type_index, type_graph, layout_cache)
    }
    /// Returns true if the underlying type is sizeless
    pub fn is_sizeless(&self, type_graph: &dyn TypeGraphLike) -> bool {
        self.base_type(type_graph).is_sizeless(type_graph)
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
    pub fn this_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> Option<&'a Type> {
        self.this_type_index.map(|x| type_graph.type_by_index(x))
    }
    /// Returns the return value type for this function type
    pub fn return_value_type<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> &'a Type {
        type_graph.type_by_index(self.return_value_type_index)
    }
    /// Returns the argument types for this function type
    pub fn argument_types<'a>(&self, type_graph: &'a dyn TypeGraphLike) -> Vec<&'a Type> {
        self.argument_type_indices.iter().map(|x| type_graph.type_by_index(*x)).collect()
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
    Enum(EnumType),
}
impl Type {
    /// Returns the size and alignment of this type
    pub fn size_and_alignment(type_index: usize, type_graph: &dyn TypeGraphLike, layout_cache: &mut TypeLayoutCache) -> anyhow::Result<(usize, usize)> {
        if let Some((existing_size, existing_alignment)) = &layout_cache.type_cache.get(&type_index) {
            return Ok((*existing_size, *existing_alignment))
        }
        let (size, alignment) = match type_graph.type_by_index(type_index) {
            Type::Primitive(primitive_type) => { let size_and_alignment = primitive_type.size_and_alignment(&layout_cache.target_triplet)?; (size_and_alignment, size_and_alignment) },
            Type::Array(array_type) => array_type.size_and_alignment(type_graph, layout_cache)?,
            Type::Pointer(pointer_type) => { let size_and_alignment = pointer_type.size_and_alignment(&layout_cache.target_triplet); (size_and_alignment, size_and_alignment) },
            Type::CVQualified(cv_qualified_type) => cv_qualified_type.size_and_alignment(type_graph, layout_cache)?,
            Type::Function(_) => { bail!("Function type is sizeless") },
            Type::UDT(udt_type) => udt_type.size_and_alignment(type_index, type_graph, layout_cache)?,
            Type::Enum(enum_type) => enum_type.size_and_alignment(&layout_cache.target_triplet)?,
        };
        layout_cache.type_cache.insert(type_index, (size, alignment));
        Ok((size, alignment))
    }
    /// Returns true if the given type is sizeless
    pub fn is_sizeless(&self, type_graph: &dyn TypeGraphLike) -> bool {
        match self {
            Type::Primitive(primitive_type) => primitive_type.is_sizeless(),
            Type::CVQualified(cv_qualified_type) => cv_qualified_type.is_sizeless(type_graph),
            Type::Function(_) => true,
            _ => false,
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
impl TypeGraphLike for TypeTree {
    fn type_by_index(&self, type_index: usize) -> &Type {
        &self.types[type_index]
    }
}
