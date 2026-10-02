verifying "bitcoin-src/src/serialize.h";

uint32 GetSizeOfCompactSize(uint64 nSize) {
    requires 4294967295u64 < nSize;
    ensures result == 9u32;
} by {
    execute();
    simp();
}
