verifying "money_nonnegative.cpp";

bool money_nonnegative(const int64& nValue) {
    owns nValue;
    ensures result == (if old(nValue) >= 0i64 { 1 } else { 0 });
} by {
    if nValue >= 0i64 {
        step_until(function.exit);
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}
