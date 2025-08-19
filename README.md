# Gospel Type Layout Language Toolkit

Gospel is a Domain Specific Language (DSL) for describing C and C++ data structure layouts and their relations to each other.
Type definitions in Gospel are evaluated dynamically in runtime based on the inputs provided to the source code 
(such as target triplet which defines the ABI for the target OS and architecture), and resulting type
definitions can be used to generate code in statically typed languages, generate bindings for such types, or read
their data in memory in runtime.

## Syntax

Gospel is a superset of C++ type layout language, which means that most of its syntax is highly similar to C++.
The following are the differences from C++:
 - Access Modifiers (public, protected, private) are not part of the language
 - Template Specializations are not supported (Templates themselves are supported though)
 - Constexpr C++ code is unsupported (Gospel has its own expression grammar distinct from C++)
 - All places where C++ expects type literals accept type expressions in Gospel
 - `alignas(N)` and base class list (`A : B, C`) support postfix conditional grammar (`class A : B if (condition)`)
 - `#pragma pack(N)` uses distinct syntax (`struct member_pack(N) A`) from C++ that is a part of struct definition
 - Only virtual functions definitions are allowed, and functions definitions cannot contain code.
 - Type aliases use keyword `type` instead of `using` and `typedef` (`type Alias = int;`)
 - Only `int` and `typename` are supported as template declaration argument types.
 - Only `constexpr` of type `int` are allowed (`constexpr int MyConstant = 5;`)
 - Field and function declarations inside types can be arranged in blocks and gated behind conditionals (`struct A { if (B == 5) int C; };`)
 - `#include` statements are replaced with `import` statements specifying name of declaration to be imported (`import A::B::C;`)

## CLI

```console
Usage: gospel-compiler.exe <COMMAND>

Commands:
  assemble  Assembles low level gospel assembly source files to a module container
  call      Call a named function with the provided arguments
  reflect   Prints information about the public interface of the given module. Note that this will not print any private module definitions or data
  parse     Parses the source file to an AST and dumps it to the standard output as JSON
  compile   Compiles module files into a module container
  eval      Compiles input files and evals an expression against them, and returns the result
  help      Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

### eval

```console
gospel-compiler eval -i tests/minimal_module.gs -e minimal_module::Test
[TREE ROOT] Type #0 (alignment: 0x8; size: 0x8): 
 | {
 |   "UDT": {
 |     "kind": "Struct",
 |     "name": "Test",
 |     "user_alignment": null,
 |     "member_pack_alignment": null,
 |     "base_class_indices": [],
 |     "members": [
 |       {
 |         "Field": {
 |           "name": "Unknown",
 |           "user_alignment": null,
 |           "member_type_index": 1
 |         }
 |       }
 |     ]
 |   }
 | }
 # UDT Layout:
 # {
 #   "alignment": 8,
 #   "unaligned_size": 8,
 #   "size": 8,
 #   "vtable": null,
 #   "base_class_offsets": [],
 #   "member_layouts": [
 #     {
 #       "Field": {
 #         "offset": 0,
 #         "alignment": 8,
 #         "size": 8
 #       }
 #     }
 #   ]
 # }
Type #1 (alignment: 0x8; size: 0x8):
 | {
 |   "Pointer": {
 |     "pointee_type_index": 2,
 |     "is_reference": false
 |   }
 | }
Type #2 (alignment: 0x0; size: 0x0):
 | {
 |   "Primitive": "Void"
 | }
```