long explicit_cast(unsigned long value) noexcept { return static_cast<long>(value); }
long implicit_cast(unsigned long value) noexcept { return value; }
long arithmetic(unsigned long value) noexcept { return static_cast<long>(value) + 1L; }
long signed_round_trip(long value) noexcept { return static_cast<long>(static_cast<unsigned long>(value)); }
unsigned long unsigned_round_trip(unsigned long value) noexcept { return static_cast<unsigned long>(static_cast<long>(value)); }
long relay(unsigned long value, int* untouched) noexcept {
    long result = explicit_cast(value);
    return result;
}
// Synthetic prerequisites: preserve EvaluateFee's fast-path expressions and
// signed return type. The upstream wide fallback remains unsupported.
template<bool RoundDown>
long fee(long fee, int at_size, int size) noexcept {
    if constexpr (RoundDown) {
        return (static_cast<unsigned long>(fee) * at_size) / static_cast<unsigned int>(size);
    } else {
        return (static_cast<unsigned long>(fee) * at_size + size - 1U) / static_cast<unsigned int>(size);
    }
}
long fee_down(long fee_value, int at_size, int size) noexcept {
    long result = fee<true>(fee_value, at_size, size);
    return result;
}
long fee_up(long fee_value, int at_size, int size) noexcept {
    long result = fee<false>(fee_value, at_size, size);
    return result;
}
