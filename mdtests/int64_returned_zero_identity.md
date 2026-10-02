# Signed 64-bit returned-zero identities

A modular helper's zero result can be added to any int64, including either
extreme. The common kernel retains the helper equality as proof provenance.

```c filename=int64_returned_zero_identity.c
int64_t zero64(void) { return 0; }
int64_t returned_zero(int64_t x) {
    int64_t z = zero64();
    return x + z;
}
int64_t subtract_zero(int64_t x, int64_t z) { return x - z; }
```

```click
verifying "int64_returned_zero_identity.c";

int64 zero64() { ensures result == 0i64; } by { execute(); simp(); }

int64 returned_zero(int64 x) {
    ensures result == x;
} by { execute(); simp(); }

int64 subtract_zero(int64 x, int64 z) {
    requires z == 0i64;
    ensures result == x;
} by { execute(); simp(); }
```

```expect
pass
```
