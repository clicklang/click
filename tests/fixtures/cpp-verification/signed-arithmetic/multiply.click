verifying "arithmetic.cpp";

int64 multiply(int64 a, int64 b) {
    requires a == 2i64;
    requires -4611686018427387904i64 <= b;
    requires b <= 4611686018427387903i64;
    ensures result == a * b;
} by {
    execute();
    simp();
}
