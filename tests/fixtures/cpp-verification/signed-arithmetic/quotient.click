verifying "arithmetic.cpp";

int64 quotient(int64 n, int64 d) {
    requires d > 0i64;
    ensures result == n / d;
} by {
    execute();
    simp();
}
