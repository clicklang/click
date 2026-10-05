// Synthetic C++20 scalar division; retain compiler-resolved promotions.
__int128 signed_quotient(__int128 a, __int128 b) noexcept { return a / b; }
__int128 signed_remainder(__int128 a, __int128 b) noexcept { return a % b; }
unsigned __int128 unsigned_quotient(unsigned __int128 a, unsigned __int128 b) noexcept { return a / b; }
unsigned __int128 unsigned_remainder(unsigned __int128 a, unsigned __int128 b) noexcept { return a % b; }
__int128 signed_relay(__int128 a, __int128 b, int* untouched) noexcept { return signed_quotient(a, b); }
unsigned __int128 mixed_quotient(long a, unsigned __int128 b) noexcept { return a / b; }
__int128 narrow_divisor(__int128 a, long b) noexcept { return a / b; }
__int128 constant_signed() noexcept { __int128 a = -7; __int128 b = 3; return a % b; }
unsigned __int128 constant_unsigned() noexcept {
    unsigned __int128 a = static_cast<unsigned __int128>(-1L);
    unsigned __int128 b = 3;
    return a / b;
}
unsigned __int128 mixed_constant() noexcept {
    long a = -1;
    unsigned __int128 b = 3;
    return a / b;
}
