verifying "split.rs";
uint64 left_length(const uint8* bytes, uint64 bytes_len, uint64 mid) {
    requires mid == 0u64;
    ensures result == 0u64;
} by { execute(); simp(); }
uint64 right_length(const uint8* bytes, uint64 bytes_len, uint64 mid) {
    requires bytes_len == 8u64;
    requires mid == 8u64;
    ensures result == 0u64;
} by { execute(); simp(); }
