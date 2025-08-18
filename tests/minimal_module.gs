// Definitions for types with explicit sizes
type int8_t = char;
type uint8_t = unsigned char;
type int16_t = short int;
type uint16_t = unsigned short int;
type int32_t = int;
type uint32_t = unsigned int;
type int64_t = long long int;
type uint64_t = unsigned long long int;

type intptr_t = if (__address_size == 8) int64_t else int32_t;
type uintptr_t = if (__address_size == 8) uint64_t else uint32_t;

/* Test block comment */
template<typename T>
struct TVector {
    T X;
    T Y;
    T Z;
};

/*
 * Test multi-line block comment
 */
type FVector = TVector<double>;

public struct FScriptElement {};

template<typename InIndexType>
public struct TSizedHeapAllocator {
    type IndexType = InIndexType;
    FScriptElement* Data;
};

template<typename InElementType, typename InAllocator = TSizedHeapAllocator<int32_t>>
public struct TArray {
    type ElementType = InElementType;
    type IndexType = InAllocator::typename IndexType;

    InAllocator AllocatorInstance;
    InAllocator::typename IndexType ArrayNum;
    InAllocator::typename IndexType ArrayMax;

    if (InElementType == int32_t) {
        template<typename T>
        local type TemplatedData = T;
    }
};

internal type FArrayOfInt32 = TArray<int32_t>;

class UObject {
    UObject* OuterPrivate;
    UClass* ClassPrivate;
    int32_t InternalIndex;
    uint32_t FlagsPrivate;
};

class UField : UObject {};
class UStruct : UField {};
class UClass : UStruct {};

type Test1 = TArray<int32_t>::typename TemplatedData<char>;
type Test2 = TArray<float>::typename TemplatedData<char>;

struct Test {
    void* Unknown;
};

struct alignas(int) EmptyStruct {};
constexpr int SizeofEmptyStruct = sizeof(EmptyStruct);

template<int Test = 5> struct TemplateWithDefault {};
type DefaultInstantiation = TemplateWithDefault<>;

template<int Condition>
struct ConditionalParentStruct : TArray<int32_t> if (Condition == 1), EmptyStruct {};

type ConditionalParentStruct1 = ConditionalParentStruct<1>;
type ConditionalParentStruct2 = ConditionalParentStruct<2>;

union TestUnion {
    long long int Test1;
    short int Test2;
    void* Test3;
    char Test4;
};
constexpr int SizeofTestUnion = sizeof(TestUnion const *volatile const);
constexpr int ConstEqualityTest = TestUnion const == TestUnion;

template<int Condition>
struct member_pack(2) if (Condition == 1) alignas(4) if (Condition == 1) TestAlignmentStruct {
    long long int TestMember;
};
constexpr int TestAlignmentStruct1 = alignof(TestAlignmentStruct<1>);
constexpr int TestAlignmentStruct2 = alignof(TestAlignmentStruct<2>);
