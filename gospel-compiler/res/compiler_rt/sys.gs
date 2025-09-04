
/// Constants for target architectures
internal constexpr unsigned long long int ARCH_X86_64 = 0;
internal constexpr unsigned long long int ARCH_ARM64 = 1;
internal constexpr unsigned long long int ARCH_ARM64EC = 2;

/// Constants for target operating systems
internal constexpr unsigned long long int OS_NONE = 0;
internal constexpr unsigned long long int OS_WIN32 = 1;
internal constexpr unsigned long long int OS_LINUX = 2;
internal constexpr unsigned long long int OS_DARWIN = 3;

/// Constants for target environments
internal constexpr unsigned long long int ENV_MSVC = 0;
internal constexpr unsigned long long int ENV_GNU = 1;
internal constexpr unsigned long long int ENV_MACHO = 2;
internal constexpr unsigned long long int ENV_ANDROID = 3;

/// Expose target properties to gospel source code by wrapping compiler builtins
internal constexpr unsigned long long int arch = __compiler_builtin(TargetArch);
internal constexpr unsigned long long int os = __compiler_builtin(TargetOS);
internal constexpr unsigned long long int env = __compiler_builtin(TargetEnv);
internal constexpr unsigned long long int address_size = __compiler_builtin(AddressSize);
