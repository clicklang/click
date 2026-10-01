# Unsigned operand bounds survive casts and widening

A byte cast to unsigned retains its range. The checker combines indexed
unsigned bounds with zero extension to prove a wide sum's upper bound,
including a word in the upper half of `uint32`. The adjacent failing case
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
    execute();
    have result <= 4294967295i64 by {
        simp() using { ((uint32)byte) <= 255u32; sum <= 4294967040u32; }
    }
    have result <= 4294967295i64 by {
        arithmetic_certificate special {
            premise 0: ((uint32)byte) <= 255u32 => ((uint32)byte) <= 255u32;
            premise 1: sum <= 4294967040u32 => sum <= 4294967040u32;
            unsigned_sum_bound bounds [0, 1] => result <= 4294967295i64;
            conclusion 0;
        }
    }
    simp();
}
```

```expect
pass
```
