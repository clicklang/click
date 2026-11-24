# Unsigned operand bounds survive casts and widening

A byte cast to unsigned retains its range. Solve expands the wide sum's
upper bound into widening identities and ordinary Integer arithmetic using
the selected unsigned bounds, including a word in the upper half of `uint32`. The adjacent failing case
must not justify a bound one smaller than the maximum possible sum.

```c filename=widened_unsigned_sum_bounds.c
long add_byte(unsigned sum, unsigned char byte) {
    unsigned word = (unsigned)byte;
    long wide = (long)sum + (long)word;
    return wide;
}
```

```click
verifying "widened_unsigned_sum_bounds.c";
int64 add_byte(uint32 sum, uint8 byte) {
    requires sum <= 4294967040u32;
    ensures result <= 4294967295i64;
} by {
    step_until(function.exit);
    have result <= 4294967295i64 by {
        close() using { (byte as uint32) <= 255u32; sum <= 4294967040u32; };
    }
    have result <= 4294967295i64 by {
        close() using { (byte as uint32) <= 255u32; sum <= 4294967040u32; };
    }
    solve();
}
```

```expect
pass
```
