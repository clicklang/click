// Synthetic ordering prerequisite. The unchanged Bitcoin wide/Assume path
// still requires support; this is not a translation of that implementation.
struct Fee {
    long fee;
    int size;
    static long Mul(long fee, int at_size) noexcept { return fee * long(at_size); }
    static long Div(long n, int d, bool round_down) noexcept {
        long quotient = n / d;
        int remainder = int(n % d);
        return quotient + ((remainder > 0) - (remainder && round_down));
    }
    template<bool RoundDown>
    long Evaluate(int at_size) const noexcept {
        return Div(Mul(fee, at_size), size, RoundDown);
    }
    long Down(int at_size) const noexcept { return Evaluate<true>(at_size); }
    long Up(int at_size) const noexcept { return Evaluate<false>(at_size); }
};
