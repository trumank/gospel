
struct void {};
struct alignas(1) char {};
struct alignas(4) float {};
struct alignas(8) double {};

struct alignas(char) int8_t {};
struct alignas(2) int16_t {};
struct alignas(4) int32_t {};
struct alignas(8) int64_t {};
struct alignas(__address_size) intptr_t {};

struct alignas(char) uint8_t {};
struct alignas(2) uint16_t {};
struct alignas(4) uint32_t {};
struct alignas(8) uint64_t {};
/* Test block comment */
struct alignas(__address_size) uintptr_t {};

// Test single line comment
template<typename T>
struct TVector {
    T X;
    T Y;
    T Z;
};

/*
 * Test multi-line block comment
 */
using FVector = TVector<double>;

public struct FScriptElement {};

template<typename InIndexType>
public struct TSizedHeapAllocator {
    using IndexType = InIndexType;
    FScriptElement* Data;
};

template<typename InElementType, typename InAllocator = TSizedHeapAllocator<int32_t>>
public struct TArray {
    using ElementType = InElementType;
    using IndexType = InAllocator::typename IndexType;

    InAllocator AllocatorInstance;
    InAllocator::typename IndexType ArrayNum;
    InAllocator::typename IndexType ArrayMax;

    if (InElementType == int32_t) {
        template<typename T>
        local using TemplatedData = T;
    }
};

internal using FArrayOfInt32 = TArray<int32_t>;

using Test1 = TArray<int32_t>::typename TemplatedData<char>;
using Test2 = TArray<float>::typename TemplatedData<char>;
