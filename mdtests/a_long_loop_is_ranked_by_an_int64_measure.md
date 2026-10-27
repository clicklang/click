# A long loop is ranked by an Integer difference

`last` walks a byte range two at a time with a `long` index. Its measure,
`length - i`, is an exact Integer difference. It owes nonnegativity and
strict descent at the back edge. The native 64-bit counter bounds are
proved by `solve() using`; they justify the increment's Integer identity.

`an_int64_measure_that_may_be_negative_is_refused.md` retains the refusal
when the last step can take the measure below zero.

```c filename=a_long_loop_is_ranked_by_an_int64_measure.c
unsigned char last(const unsigned char *bytes, long length) {
    unsigned char v = 0;
    for (long i = 0; i + 1 < length; i += 2) {
        v = bytes[i + 1];
    }
    return v;
}
```

```click
verifying "a_long_loop_is_ranked_by_an_int64_measure.c";

uint8 last(const uint8* bytes, int64 length) {
    requires 0i64 <= length;
    requires length <= 2147483647i64;
    views bytes[0..length];
    ensures result == result;
} by {
    step_until(loop(0));
    loop {
        decreases length - i;
        views bytes[0..length];
        invariant length <= 2147483647i64;
        invariant 0i64 <= i;
        invariant i <= length;
        invariant i <= 2147483647i64;
        preserve by {
            have to_integer(i + 2i64) <= to_integer(length) by {
                solve() using { 0i64 <= i; i <= length; to_integer(i + 1i64) < to_integer(length); length <= 2147483647i64; };
            }
            have to_integer(length - (i + 2i64)) < to_integer(length - i) by {
                solve() using { 0i64 <= i; i <= length; to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; };
            }
            have to_integer(0i64) <= to_integer(i + 2i64) by {
                solve() using { 0i64 <= i; i <= length; length <= 2147483647i64; };
            }
            have to_integer(i + 2i64) <= to_integer(2147483647i64) by {
                solve() using { to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; 0i64 <= i; i <= length; };
            }
            have to_integer(0i64) <= to_integer(length - (i + 2i64)) by {
                solve() using { to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; 0i64 <= i; i <= length; };
            }
            have to_integer(0i64) <= to_integer(i + 1i64) by {
                solve() using { 0i64 <= i; i <= length; length <= 2147483647i64; };
            }
            step(); step();
            solve();
        }
    }
}
```

```expect
pass
```
