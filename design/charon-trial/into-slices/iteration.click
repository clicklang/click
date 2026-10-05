verifying "iteration.rs";
uint8 first_byte(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 1u64;
    views bytes[0..1];
    ensures result == old(bytes[0]);
} by { execute(); simp(); }
int32 first_signed(const int32* values, uint64 values_len) {
    requires values_len == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
uint32 first_unsigned(const uint32* values, uint64 values_len) {
    requires values_len == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
int32 forward_signed(const int32* values, uint64 values_len) {
    requires values_len == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
