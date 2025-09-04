import module::minimal_module::{uint64_t, int32_t};

struct MinimalStruct {
    uint64_t A;
    int32_t B;
};

enum TestUnscopedEnum {
    InitialConstant,
    NextConstant,
    ConstantWithValue = 0x50,
    ConstantWithoutValue if (sizeof(MinimalStruct) == 16),
};

enum class SuperLargeEnum : unsigned long long int {
    SuperLargeConstant = 1u64 << 46,
    NextConstant,
};

enum class TestScopedEnum : uint64_t {
    InitialValue
};

constexpr int SwitchStatementTest = switch(sys::os) {
    sys::OS_LINUX => 500,
    _ => 3333,
};

class FuncPtrTest {
    void(*)(int, char*, FuncPtrTest*) GlobalFunctionPtr;
    void(*const)(int, char*, FuncPtrTest*) GlobalConstFunctionPtr;
    char*(FuncPtrTest::*)() MemberFunctionPtr;
    char*(FuncPtrTest::*const)() MemberConstFunctionPtr;
};
