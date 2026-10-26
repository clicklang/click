verifying "at_least_one_coin.cpp";

bool at_least_one_coin(const int64& value) {
    owns value;
    ensures result == (if old(value) >= 100000000i64 { 1 } else { 0 });
} by {
    if value >= 100000000i64 {
        step_until(function.exit);
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}
