# arithmetic proves int64 order goals

`arithmetic() using` reads a signed 64-bit order goal as it reads an
unsigned one, through the exact Integer observations of its operands
(`mdtests/a_size_t_loop_stepping_by_two_closes_with_arithmetic.md`). The
difference is what a sum owes. An unsigned sum wraps, so it is observed
term by term once it is shown not to exceed the type. A signed sum that
leaves its range is undefined, so it is shown defined first, from both
Integer bounds, by `int64_add_defined_by_integer_bounds`; a premise over a
sum is carried to Integer order only after that.

`step_two` is the fact a `long` loop stepping by two owes at its back edge.
`chain` needs no sum. `difference` bounds a difference from above.

`an_int64_sum_that_may_overflow_is_not_arithmetic.md` leaves out the lower
bound.

```click
theorem step_two(i: int64, length: int64) {
    requires 0i64 <= i;
    requires i <= length;
    requires i + 1i64 < length;
    requires length <= 2147483647i64;
    ensures i + 2i64 <= length by {
        arithmetic() using { 0i64 <= i; i <= length; i + 1i64 < length; length <= 2147483647i64; }
    }
}

theorem chain(i: int64, n: int64, length: int64) {
    requires i < n;
    requires n <= length;
    ensures i < length by {
        arithmetic() using { i < n; n <= length; }
    }
}

theorem difference(i: int64, length: int64) {
    requires 0i64 <= i;
    requires i <= length;
    requires length <= 1000i64;
    ensures length - i <= 1000i64 by {
        arithmetic() using { 0i64 <= i; i <= length; length <= 1000i64; }
    }
}
```

```expect
pass
```
