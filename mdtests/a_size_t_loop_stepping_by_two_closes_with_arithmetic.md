# A size_t loop stepping by two closes with arithmetic

The loop of `a_size_t_loop_stepping_by_two_closes_with_explicit_steps.md`,
with each of its two 64-bit facts proved by one `arithmetic() using`.

`arithmetic` reads a `uint64` order goal through the exact Integer
observations of its operands. It carries each listed 64-bit premise to
Integer order, shows that each sum and difference in the premises and the
goal does not wrap, proves the Integer claim, and carries it back. The
steps are the bridge theorems the other file applies by hand, and
`click expand` writes them out.

`a_uint64_sum_that_may_wrap_is_not_arithmetic.md` leaves out the premise
that keeps a sum in range.

```c filename=a_size_t_loop_stepping_by_two_closes_with_arithmetic.c
unsigned char last(const unsigned char *bytes, unsigned long length) {
    unsigned char v = 0;
    for (unsigned long i = 0; i + 1 < length; i += 2) {
        v = bytes[i + 1];
    }
    return v;
}
```

```click
verifying "a_size_t_loop_stepping_by_two_closes_with_arithmetic.c";

uint8 last(const uint8* bytes, uint64 length) {
    requires length <= 2147483647u64;
    views bytes[0..length];
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases length - i;
        views bytes[0..length];
        invariant length <= 2147483647u64;
        invariant i <= length;
        preserve by {
            have i + 2u64 <= length by {
                arithmetic() using { i <= length; i + 1u64 < length; length <= 2147483647u64; }
            }
            have length - (i + 2u64) < length - i by {
                arithmetic() using { i <= length; i + 2u64 <= length; length <= 2147483647u64; }
            }
            step(); step();
            simp();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
