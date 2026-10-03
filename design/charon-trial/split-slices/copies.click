verifying "copies.rs";
uint64 copy_right(const uint8* bytes, uint64 bytes_len, uint64 mid) {
    requires mid <= bytes_len;
    requires mid <= 2147483647u64;
    ensures result == bytes_len - mid;
} by { execute(); simp(); }
uint64 reassign_left(const uint8* bytes, uint64 bytes_len, uint64 mid) {
    requires mid <= bytes_len;
    requires mid <= 2147483647u64;
    ensures result == 0u64;
} by { execute(); simp(); }
uint64 collision(const uint8* bytes, uint64 bytes_len, uint64 mid) {
    requires mid <= bytes_len;
    requires mid <= 2147483647u64;
    ensures result == bytes_len - mid;
} by { execute(); simp(); }
