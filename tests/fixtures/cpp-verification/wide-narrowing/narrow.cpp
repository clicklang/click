// Synthetic C++20 casts preserving the narrowing pattern in FeeFrac::Div.
long ss64(__int128 a) noexcept { return a; }
int ss32(__int128 a) noexcept { return static_cast<int>(a); }
unsigned long su64(__int128 a) noexcept { return a; }
unsigned int su32(__int128 a) noexcept { return static_cast<unsigned int>(a); }
long us64(unsigned __int128 a) noexcept { return a; }
int us32(unsigned __int128 a) noexcept { return static_cast<int>(a); }
unsigned long uu64(unsigned __int128 a) noexcept { return a; }
unsigned int uu32(unsigned __int128 a) noexcept { return static_cast<unsigned int>(a); }
long quotient(__int128 a, __int128 b) noexcept { return a / b; }
int remainder(__int128 a, __int128 b) noexcept { return a % b; }
long relay(__int128 a, int* untouched) noexcept { return ss64(a); }
long unsafe_operand(__int128 a, __int128 b) noexcept { return a / b; }
long wrap_high() noexcept {
    __int128 high = static_cast<__int128>(4294967296L) * 4294967296L;
    return high;
}
unsigned long wrap_negative() noexcept { __int128 a = -1; return a; }
long wrap_unsigned_max() noexcept { unsigned __int128 a = static_cast<unsigned __int128>(-1L); return a; }
