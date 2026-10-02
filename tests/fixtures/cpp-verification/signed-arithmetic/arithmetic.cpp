// The correction expression is the one used by Bitcoin Core's FeeFrac::Div.
// This synthetic fixture uses a signed 64-bit dividend; upstream uses __int128.
long rounded_divide(long n, int d, bool round_down) noexcept {
    long quot = n / d;
    int mod = n % d;
    return quot + ((mod > 0) - (mod && round_down));
}

long quotient(long n, long d) noexcept { return n / d; }
long remainder(long n, long d) noexcept { return n % d; }
long multiply(long a, long b) noexcept { return a * b; }
long negate(long n) noexcept { return -n; }
int narrow(long n) noexcept { return static_cast<int>(n); }

long relay(long n, long d, int& untouched) noexcept {
    long captured = quotient(n, d);
    return captured;
}
