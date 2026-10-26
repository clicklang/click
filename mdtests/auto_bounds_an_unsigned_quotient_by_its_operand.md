# The implicit closer bounds an unsigned quotient, shift, or remainder by its operand

An unsigned quotient by a constant is the floor of the division, so
`c * (x / c) <= x <= c * (x / c) + (c - 1)`; a logical right shift by a
constant `k` is that quotient with `c = 2^k`; and `x % c <= c - 1`. The implicit closer's
solver takes these bounds for every such operation among its facts' and
goal's terms, as it takes a machine value's type range. An unsigned value
that differs from zero, its type's minimum, is at least one.

Together they read the guard of Linux's `while (blk_size >> 32)` as
`4294967296 <= blk_size`, and bound what the loop divides.

```click
theorem shifted_guard(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 4294967296u64 <= v;
}

theorem shifted_is_at_least_one(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 1u64 <= (v >> 32);
}

theorem small_shifts_to_zero(v: uint64) {
    requires v < 4294967296u64;
    ensures (v >> 32) == 0u64;
}

theorem quotient_floor(v: uint64) {
    requires 4294967296u64 <= v;
    ensures 4294967u64 <= v / 1000u64;
}

theorem quotient_decreases(v: uint64) {
    requires 1u64 <= v;
    ensures v / 1000u64 < v;
}

theorem remainder_below_divisor(v: uint64) {
    ensures v % 1000u64 < 1000u64;
}

theorem uint32_shift(v: uint32) {
    requires (v >> 16) != 0u32;
    ensures 65536u32 <= v;
}
```

```expect
pass
```
