# Signed 64-bit scalar arithmetic

A positive divisor excludes zero and the sole signed division overflow pair.
Subtracting a value from itself is defined across the entire signed range.
These checks use the common kernel shared by the C and C++ import paths.

```c filename=int64_checked_scalar_arithmetic.c
int64_t quotient(int64_t n, int64_t d) { return n / d; }
int64_t remainder(int64_t n, int64_t d) { return n % d; }
int64_t clear64(int64_t n) { return n - n; }
int clear32(int n) { return n - n; }
```

```click
verifying "int64_checked_scalar_arithmetic.c";

int64 quotient(int64 n, int64 d) {
    requires d > 0i64;
    ensures result == n / d;
} by { execute(); simp(); }

int64 remainder(int64 n, int64 d) {
    requires d > 0i64;
    ensures result == n % d;
} by { execute(); simp(); }

int64 clear64(int64 n) {
    ensures result == 0i64;
} by { execute(); simp(); }

int32 clear32(int32 n) {
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
