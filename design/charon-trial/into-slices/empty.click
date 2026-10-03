verifying "iteration.rs";
uint8 first_byte(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 0u64;
    ensures result == 0;
} by { execute(); simp(); }
int32 first_signed(const int32* values, uint64 values_len) {
    requires values_len == 0u64;
    ensures result == 0;
} by { execute(); simp(); }
uint32 first_unsigned(const uint32* values, uint64 values_len) {
    requires values_len == 0u64;
    ensures result == 0u32;
} by { execute(); simp(); }
