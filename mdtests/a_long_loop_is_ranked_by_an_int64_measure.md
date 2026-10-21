# A long loop is ranked by an int64 measure

`last` walks a byte range two at a time with a `long` index. Its measure,
`length - i`, is an `int64`: a ranked carrier beside `int32`, `uint32` and
`uint64`. It is ranked by signed 64-bit order and, like an `int32` measure,
owes `0 <= length - i` at the back edge, because a signed value is not a
natural number by construction.

The 64-bit facts the back edge owes are each one `arithmetic() using`
(`mdtests/arithmetic_proves_int64_order_goals.md`).
`a_size_t_loop_stepping_by_two_closes_with_arithmetic.md` is the same loop
with an unsigned index, which owes no lower bounds.

`an_int64_measure_that_may_be_negative_is_refused.md` is a loop whose
measure the last step can take below zero, which is refused.

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
    execute_until(loop(0));
    loop {
        decreases length - i;
        views bytes[0..length];
        invariant length <= 2147483647i64;
        invariant 0i64 <= i;
        invariant i <= length;
        invariant i <= 2147483647i64;
        preserve by {
            have to_integer(i + 2i64) <= to_integer(length) by {
                arithmetic() using { 0i64 <= i; i <= length; to_integer(i + 1i64) < to_integer(length); length <= 2147483647i64; };
            }
            have to_integer(length - (i + 2i64)) < to_integer(length - i) by {
                arithmetic() using { 0i64 <= i; i <= length; to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; };
            }
            have to_integer(0i64) <= to_integer(i + 2i64) by {
                arithmetic() using { 0i64 <= i; i <= length; length <= 2147483647i64; };
            }
            have to_integer(i + 2i64) <= to_integer(2147483647i64) by {
                arithmetic() using { to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; 0i64 <= i; i <= length; };
            }
            have to_integer(0i64) <= to_integer(length - (i + 2i64)) by {
                arithmetic() using { to_integer(i + 2i64) <= to_integer(length); length <= 2147483647i64; 0i64 <= i; i <= length; };
            }
            have to_integer(0i64) <= to_integer(i + 1i64) by {
                arithmetic() using { 0i64 <= i; i <= length; length <= 2147483647i64; };
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
