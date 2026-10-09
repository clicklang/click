# An int64 measure that may be negative is refused

The loop of `a_long_loop_is_ranked_by_an_int64_measure.md` without the fact
`0 <= length - (i + 2)`. A signed measure owes its lower bound at the back
edge: descent through negative values is not well founded. The closer does
not find the bound on its own, and the loop is refused.

```c filename=an_int64_measure_that_may_be_negative_is_refused.c
unsigned char last(const unsigned char *bytes, long length) {
    unsigned char v = 0;
    for (long i = 0; i + 1 < length; i += 2) {
        v = bytes[i + 1];
    }
    return v;
}
```

```click
verifying "an_int64_measure_that_may_be_negative_is_refused.c";

uint8 last(const uint8* bytes, int64 length) {
    requires 0i64 <= length;
    requires length <= 2147483647i64;
    views bytes[0..length];
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases length - i;
        views bytes[0..length];
        invariant length <= 2147483647i64;
        invariant 0i64 <= i;
        invariant i <= length;
        invariant i <= 2147483647i64;
        preserve by {
            have i + 2i64 <= length by {
                arithmetic() using { 0i64 <= i; i <= length; i + 1i64 < length; length <= 2147483647i64; }
            }
            have length - (i + 2i64) < length - i by {
                arithmetic() using { 0i64 <= i; i <= length; i + 2i64 <= length; length <= 2147483647i64; }
            }
            have 0i64 <= i + 2i64 by {
                arithmetic() using { 0i64 <= i; i <= length; length <= 2147483647i64; }
            }
            have i + 2i64 <= 2147483647i64 by {
                arithmetic() using { i + 2i64 <= length; length <= 2147483647i64; 0i64 <= i; i <= length; }
            }
            have 0i64 <= i + 1i64 by {
                arithmetic() using { 0i64 <= i; i <= length; length <= 2147483647i64; }
            }
            step(); step();
            simp();
        }
    }
    execute(); simp();
}
```

```expect
fail: closure body did not prove every invariant obligation
```
