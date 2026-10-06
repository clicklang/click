// Retain the arithmetic and short-circuit pattern of Bitcoin FeeFrac::Div.
long rounded(__int128 n, int d, bool round_down) noexcept {
    long quot = n / d;
    int mod = n % d;
    return quot + ((mod > 0) - (mod && round_down));
}
long caller(__int128 n, int d, bool round_down, int* untouched) noexcept {
    return rounded(n, d, round_down);
}
