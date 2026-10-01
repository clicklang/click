verifying "arrays.rs";

uint8 first(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len > 0u64;
    requires bytes_len <= 2147483647u64;
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
void set(uint8* bytes, uint64 bytes_len) {
    requires bytes_len > 1u64;
    requires bytes_len <= 2147483647u64;
    owns bytes[1..2];
    ensures bytes[1] == 7;
} by { execute(); simp(); }
uint64 size(const uint8* bytes, uint64 bytes_len) {
    ensures result == bytes_len;
} by { execute(); simp(); }
uint64 array_len(const uint8* bytes) { ensures result == 3u64; } by { execute(); simp(); }
uint8 read(const uint8* bytes) {
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
uint8 mutate(uint8* bytes) {
    owns bytes[1..2];
    ensures result == 7;
} by { execute(); simp(); }
uint8 local() { ensures result == 10; } by { execute(); simp(); }
uint8 alias(uint8* bytes) {
    owns bytes[1..2];
    ensures result == 7;
} by { execute(); simp(); }
uint64 retarget() { ensures result == 4u64; } by { execute(); simp(); }
uint8 retarget_mut() { ensures result == 14; } by { execute(); simp(); }
uint64 empty() { ensures result == 0u64; } by { execute(); simp(); }
uint64 empty_ref(const uint8* bytes) { ensures result == 0u64; } by { execute(); simp(); }
uint8 borrow_shared(uint8* bytes) {
    owns bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
