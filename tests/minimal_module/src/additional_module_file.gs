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

enum class TestScopedEnum : uint64_t {
    InitialValue
};
