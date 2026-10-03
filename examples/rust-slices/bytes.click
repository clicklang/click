verifying "bytes.rs";

uint64 length(const uint8* bytes, uint64 bytes_len) {
    ensures result == bytes_len;
} by { execute(); simp(); }

uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }

void write(uint8* bytes, uint64 bytes_len, uint64 index, uint8 value) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    owns bytes[0..(int32)bytes_len];
    ensures bytes[(int32)index] == value;
} by { execute(); simp(); }

uint8 first(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 4u64;
    views bytes[0..4];
    ensures result == bytes[0];
} by { execute(); simp(); }

void increment_first(uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 4u64;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by { execute(); simp(); }

bool empty(const uint8* bytes, uint64 bytes_len) {
    ensures result == (if bytes_len == 0u64 { 1 } else { 0 });
} by {
    if bytes_len == 0u64 { execute(); simp(); }
    else { execute(); simp(); }
}
