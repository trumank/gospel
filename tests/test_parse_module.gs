import unreal;

input int UE_VERSION_MAJOR = 5;
input int UE_WITH_CASE_PRESERVING_NAME;
input int UE_NAME_OUTLINE_NUMBER;

type FReal = if (UE_VERSION_MAJOR == 5) double else float;
type FPartialIdentifierTest = float;

namespace A::B {
    namespace C {
        struct FNoncopyable {
        };
    };
};

struct FNameEntryId {
    uint32 Value;
};

struct FName {
    FNameEntryId ComparisonIndex;
    if (UE_WITH_CASE_PRESERVING_NAME) {
        FNameEntryId DisplayIndex;
    }
    if (!UE_NAME_OUTLINE_NUMBER) {
        uint32 Number;
    }
};

template<typename KeyType, typename ValueType>
struct TPair {
    KeyType Key;
    ValueType Value;
};

template<typename T>
struct TVector {
    type ElementType = T;
    T X;
    T Y;
    T Z;
};
type FVector = TVector<FReal>;

type TestMemberAccessOperator1 = FVector::typename ElementType;
type TestMemberAccessOperator2 = FVector::typename X;

struct FConditionalStructTest : if (UE_VERSION_MAJOR == 5) AInfo else AActor {
    if (UE_VERSION_MAJOR != 5) {
        uint32 Test: 5;
    } else if (UE_VERSION_MINOR == 26) {
        uint16 Test[5];
    } else {
        uint8 Test;
    }
    if (UE_WITH_CASE_PRESERVING_NAME) {
        FName Name;
    } else if (!UE_NAME_OUTLINE_NUMBER) {
        uint32 Number;
    }
};

template<typename Ignored>
struct FWrapperStruct {
    template<typename InInnerType>
    type Inner = InInnerType;
};

type DynamicTemplateInstantiationTest = FWrapperStruct<FVector>::typename Inner<float>;

constexpr int ComplexExpressionTest = {
    let int LocalVariable = UE_VERSION_MINOR;
    LocalVariable += 5;
    LocalVariable = LocalVariable / 1;
    let int Result = 3;
    if (LocalVariable == 4) {
        Result = sizeof(FVector);
    }
    while (LocalVariable < 100) {
        LocalVariable += 1;
        continue;
        break;
        ;
    }
    (Result[10])::int Variable
};

constexpr int SizeOfVector = sizeof(FVector);
constexpr int AlignmentOfVector = alignof(FVector);

template<typename T>
struct TTypeCompatibleBytes {
    alignas(T) char Pad[sizeof(T)];
};

template<typename ElementType>
struct THeapAllocator {
    ElementType* Data;
};

template<typename ElementType, int InlineElementCount, typename SecondaryAllocator = THeapAllocator<ElementType>>
struct TInlineAllocator {
    TTypeCompatibleBytes<ElementType> InlineData[InlineElementCount];
    SecondaryAllocator SecondaryData;
};

template<typename ElementType, typename AllocatorType = THeapAllocator<ElementType>>
struct TArray {
    AllocatorType AllocatorInstance;
    int32 ArrayNum;
    int32 ArrayMax;
};
type FByteArray = TArray<uint8>;

constexpr int BinaryOperatorPrecedenceTest = A | B ^ C & D >> E << F + G - H * I[A + B] / J % K > L < M >= N <= O && P || Q == R != S;
constexpr int UnaryOperatorTest = sizeof(A*) + alignof(B*) + ~C + -D + !E * (F + G);

;
