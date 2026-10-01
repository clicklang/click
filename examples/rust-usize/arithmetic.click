verifying "arithmetic.rs";
uint64 add(uint64 x, uint64 y) {
    requires x <= 18446744073709551615u64 - y;
    ensures result == x + y;
} by { execute(); simp(); }
uint64 sub(uint64 x, uint64 y) {
    requires x >= y;
    ensures result == x - y;
} by { execute(); simp(); }
uint64 mul(uint64 x, uint64 y) {
    requires x == 4294967296u64;
    requires y == 2147483648u64;
    ensures result == 9223372036854775808u64;
} by { execute(); simp(); }
uint64 div(uint64 x, uint64 y) {
    requires y != 0u64;
    ensures result == x / y;
} by { execute(); simp(); }
uint64 rem(uint64 x, uint64 y) {
    requires y != 0u64;
    ensures result == x % y;
} by { execute(); simp(); }
uint64 left(uint64 x, uint64 n) {
    requires x == 9223372036854775808u64;
    requires n == 1u64;
    ensures result == 0u64;
} by { execute(); simp(); }
uint64 right(uint64 x, int32 n) {
    requires x == 18446744073709551615u64;
    requires n == 63;
    ensures result == 1u64;
} by { execute(); simp(); }
uint64 bits(uint64 x) {
    requires x == 0u64;
    ensures result == 18446744069414584318u64;
} by { execute(); simp(); }
uint32 narrow(uint64 x) {
    requires x == 4294967297u64;
    ensures result == 1u32;
} by { execute(); simp(); }
uint8 byte(uint64 x) {
    requires x == 18446744073709551615u64;
    ensures result == 255;
} by { execute(); simp(); }
int32 signed(uint64 x) {
    requires x == 18446744073709551615u64;
    ensures result == -1;
} by { execute(); simp(); }
uint64 widen(uint32 x) {
    requires x == 4294967295u32;
    ensures result == 4294967295u64;
} by { execute(); simp(); }
uint64 sign_extend(int32 x) {
    requires x == -1;
    ensures result == 18446744073709551615u64;
} by { execute(); simp(); }
uint8 computed(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len == 2u64;
    requires index == 0u64;
    views bytes[0 .. 2];
    ensures result == bytes[1];
} by { execute(); simp(); }
uint64 length(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 18446744073709551614u64;
    ensures result == bytes_len + 1u64;
} by { execute(); simp(); }
