// Synthetic scalar prerequisites; Bitcoin's __int128 and Assume path is deferred.
struct FeeMath {
    static long Mul(long fee, int at_size) noexcept { return fee * long(at_size); }
    static long Div(long n, int d, bool round_down) noexcept {
        long quotient = n / d;
        int remainder = int(n % d);
        return quotient + ((remainder > 0) - (remainder && round_down));
    }
    template<bool RoundDown>
    static long Evaluate(long fee, int at_size, int divisor) noexcept {
        return Div(Mul(fee, at_size), divisor, RoundDown);
    }
};
long static_fee_down(long fee, int at_size, int divisor) noexcept {
    return FeeMath::Evaluate<true>(fee, at_size, divisor);
}
long static_fee_up(long fee, int at_size, int divisor) noexcept {
    return FeeMath::Evaluate<false>(fee, at_size, divisor);
}
struct Scalar {
    // A static call must not require importing unrelated object storage.
    __int128 unrelated;
    static int echo(int value) noexcept { return value; }
    static long echo64(long value) noexcept { return value; }
    static unsigned echo_u32(unsigned value) noexcept { return value; }
    static unsigned long echo_u64(unsigned long value) noexcept { return value; }
    static bool echo_bool(bool value) noexcept { return value; }
};
struct Other { static int echo(int value) noexcept { return value; } };
int static_chain(int value) noexcept { return Scalar::echo(Other::echo(value)); }
int static_local(int value) noexcept { int captured = Scalar::echo(value); return captured; }
struct FeeValue {
    long fee;
    long Evaluate(int at_size) const noexcept { return FeeMath::Mul(fee, at_size); }
};
