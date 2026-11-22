# Pointer subtraction returns a signed distance for wide indices

Both pointers name the same array. The view permits the endpoint to be one
past the last element. The difference counts elements even for an array of
four-byte integers.

```c filename=pointer_distance.c
#include <stddef.h>

ptrdiff_t forward(int *base, unsigned long n) {
    return (base + n) - base;
}

ptrdiff_t backward(int *base, unsigned long n) {
    return base - (base + n);
}

ptrdiff_t byte_distance(unsigned char *base, unsigned long n) {
    unsigned char *end = base + n;
    end++;
    return end - base;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "pointer_distance.c";

int64 forward(int32* base, uint64 n) {
    requires base != 0;
    requires n <= 2305843009213693951u64;
    views base[0..n];
    ensures to_integer(result) == to_integer(n);
}

int64 backward(int32* base, uint64 n) {
    requires base != 0;
    requires n <= 2305843009213693951u64;
    views base[0..n];
    ensures to_integer(result) == to_integer(0i64 - (n as int64));
}

int64 byte_distance(uint8* base, uint64 n) {
    requires base != 0;
    requires n < 2147483647u64;
    views base[0..n + 1u64];
    ensures to_integer(result) == to_integer((n as int64) + 1i64);
}
```

```expect
pass
```
