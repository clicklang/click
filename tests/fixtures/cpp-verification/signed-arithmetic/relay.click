verifying "arithmetic.cpp";

int64 quotient(int64 n, int64 d) {
    requires d > 0i64;
    ensures result == n / d;
} by {
    execute();
    simp();
}

int64 relay(int64 n, int64 d, int32* untouched) {
    requires d > 0i64;
    owns untouched[0..1];
    ensures result == n / d;
    ensures untouched[0] == old(untouched[0]);
} by {
    execute();
    simp();
}
