verifying "bitcoin-src/src/consensus/amount.h";

bool MoneyRange(const int64& nValue) {
    owns nValue;
    ensures nValue == old(nValue);
    ensures result == (if old(nValue) >= 0i64 {
        if old(nValue) <= 2100000000000000i64 { true } else { false }
    } else { false });
} by {
    if nValue >= 0i64 {
        if nValue <= 2100000000000000i64 {
            step_until(function.exit);
            solve();
        } else {
            step_until(function.exit);
            solve();
        }
    } else {
        step_until(function.exit);
        solve();
    }
}
