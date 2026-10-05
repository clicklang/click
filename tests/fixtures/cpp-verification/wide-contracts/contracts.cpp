__int128 identity(__int128 value) noexcept { return value; }
unsigned __int128 unsigned_identity(unsigned __int128 value) noexcept { return value; }
__int128 round_trip(__int128 value) noexcept {
    unsigned __int128 bits = static_cast<unsigned __int128>(value);
    return static_cast<__int128>(bits);
}
__int128 widen(long value) noexcept { return value; }
unsigned __int128 widen_unsigned(unsigned long value) noexcept { return value; }
__int128 multiply(long a, long b) noexcept { return static_cast<__int128>(a) * b; }
__int128 relay(__int128 value, int& untouched) noexcept {
    __int128 captured = identity(value);
    return captured;
}
__int128 nested(__int128 value) noexcept { return identity(identity(value)); }
unsigned __int128 unsigned_round_trip(unsigned __int128 value) noexcept {
    __int128 bits = static_cast<__int128>(value);
    return static_cast<unsigned __int128>(bits);
}
unsigned __int128 maximum() noexcept { return static_cast<unsigned __int128>(-1L); }
__int128 minimum() noexcept {
    __int128 high = static_cast<__int128>(4294967296L) * 4294967296L;
    return high * (-9223372036854775807L - 1L);
}
