verifying "arithmetic.cpp";

int64 quotient(int64 n, int64 d) {
    requires d > 0i64;
    ensures result == n / d;
} by {
    execute();
    simp();
}

int64 relay(int64 n, int64 d, int32& untouched) {
    requires d > 0i64;
    owns untouched;
    ensures result == n / d;
    ensures untouched == old(untouched);
} by {
    execute();
    simp();
}
