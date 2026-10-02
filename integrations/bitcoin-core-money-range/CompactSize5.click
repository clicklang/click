verifying "bitcoin-src/src/serialize.h";

uint32 GetSizeOfCompactSize(uint64 nSize) {
    requires 65535u64 < nSize;
    requires nSize <= 4294967295u64;
    ensures result == 5u32;
} by {
    execute();
    simp();
}
