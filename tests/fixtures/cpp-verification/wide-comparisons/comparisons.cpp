// Synthetic C++20 comparisons with explicit compiler-resolved promotions.
bool signed_equal(__int128 a, __int128 b) noexcept { return a == b; }
bool signed_less(__int128 a, __int128 b) noexcept { return a < b; }
bool signed_greater(__int128 a, __int128 b) noexcept { return a > b; }
bool signed_less_equal(__int128 a, __int128 b) noexcept { return a <= b; }
bool signed_greater_equal(__int128 a, __int128 b) noexcept { return a >= b; }
bool unsigned_equal(unsigned __int128 a, unsigned __int128 b) noexcept { return a == b; }
bool unsigned_less(unsigned __int128 a, unsigned __int128 b) noexcept { return a < b; }
bool unsigned_greater(unsigned __int128 a, unsigned __int128 b) noexcept { return a > b; }
bool unsigned_less_equal(unsigned __int128 a, unsigned __int128 b) noexcept { return a <= b; }
bool unsigned_greater_equal(unsigned __int128 a, unsigned __int128 b) noexcept { return a >= b; }
bool relay(__int128 a, __int128 b, int* untouched) noexcept { return signed_less(a, b); }
int choose(__int128 a, __int128 b) noexcept { if (a < b) { return 7; } return 11; }
bool narrow_compare(__int128 a, long b) noexcept { return a < b; }
bool mixed_constant() noexcept { long a = -1; unsigned __int128 b = 7; return a > b; }
bool high_equal_zero() noexcept {
    __int128 high = static_cast<__int128>(4294967296L) * 4294967296L;
    return high == 0;
}
bool minimum_negative() noexcept {
    __int128 high = static_cast<__int128>(4294967296L) * 4294967296L;
    __int128 low = high * (-9223372036854775807L - 1L);
    return low < 0;
}
bool unsigned_max_positive() noexcept { unsigned __int128 high = static_cast<unsigned __int128>(-1L); return high > 0; }
bool unsafe_operand(__int128 a, __int128 b) noexcept { return a / b < 0; }
bool signed_not_equal(__int128 a, __int128 b) noexcept { return a != b; }
bool unsigned_not_equal(unsigned __int128 a, unsigned __int128 b) noexcept { return a != b; }
