# Machine remainders describe complete chunks and their tail

The full-width divisor must be positive. Narrowing a complete byte prefix
also requires the original length to fit in the nonnegative signed-word range.
Subtracting a positive chunk size preserves the remainder only when the
subtraction is nonnegative.

```click
theorem tail_bounds(n: uint64, size: uint64) {
    requires 0u64 < size;
    ensures n % size <= n by { normalize() using { 0u64 < size; } }
    ensures n % size < size by { normalize() using { 0u64 < size; } }
}
theorem complete_prefix(n: uint64) {
    requires n <= 2147483647u64;
    ensures (((int32)(uint32)(n - n % 4u64)) % 4) == 0 by {
        normalize() using { n <= 2147483647u64; }
    }
}
theorem consume_chunk(n: int32) {
    requires 4 <= n;
    ensures (n - 4) % 4 == n % 4 by { normalize() using { 4 <= n; } }
}
theorem short_tail(n: int32) {
    requires 0 <= n;
    requires n < 4;
    ensures n % 4 == n by { normalize() using { 0 <= n; n < 4; } }
}
```

```expect
pass
```
