verifying "bitcoin-src/src/serialize.h";

uint32 GetSizeOfCompactSize(uint64 nSize) {
    requires nSize < 253u64;
    ensures result == 1u32;
} by {
    execute();
    simp();
}
