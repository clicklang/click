verifying "bitcoin-src/src/serialize.h";

uint32 GetSizeOfCompactSize(uint64 nSize) {
    requires 253u64 <= nSize;
    requires nSize <= 65535u64;
    ensures result == 3u32;
} by {
    execute();
    simp();
}
