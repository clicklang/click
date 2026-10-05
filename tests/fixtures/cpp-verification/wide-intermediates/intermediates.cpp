unsigned long product_low(long a, long b) noexcept {
    __int128 product = static_cast<__int128>(a) * b;
    return static_cast<unsigned long>(product);
}
bool product_truth(long a, long b) noexcept {
    __int128 product = static_cast<__int128>(a) * b;
    return static_cast<bool>(product);
}
long signed_round_trip(long value) noexcept {
    unsigned __int128 widened = static_cast<unsigned __int128>(value);
    __int128 restored = static_cast<__int128>(widened);
    return static_cast<long>(restored);
}
unsigned long unsigned_round_trip(unsigned long value) noexcept {
    __int128 widened = value;
    unsigned __int128 restored = static_cast<unsigned __int128>(widened);
    return static_cast<unsigned long>(restored);
}
unsigned long narrow_overflow(long a, long b) noexcept {
    __int128 widened = static_cast<__int128>(a * b);
    return static_cast<unsigned long>(widened);
}
bool wide_overflow(long a) noexcept {
    __int128 square = static_cast<__int128>(a) * a;
    __int128 fourth = square * square;
    return static_cast<bool>(fourth);
}
long relay(long value) noexcept { return signed_round_trip(value); }

namespace std {
template<class T> struct numeric_limits;
template<> struct numeric_limits<unsigned __int128> {
    static constexpr unsigned __int128 max() noexcept {
        return ~static_cast<unsigned __int128>(0);
    }
};
template<> struct numeric_limits<__int128> {
    static constexpr __int128 max() noexcept {
        return static_cast<__int128>((~static_cast<unsigned __int128>(0)) >> 1);
    }
};
}
unsigned long constant_low() noexcept {
    unsigned __int128 value = std::numeric_limits<unsigned __int128>::max();
    return static_cast<unsigned long>(value);
}
bool constant_high_truth() noexcept {
    __int128 value = std::numeric_limits<__int128>::max();
    return static_cast<bool>(value);
}
