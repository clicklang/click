# A uint64 equality closes with arithmetic

`arithmetic() using` proves a 64-bit equality as it proves a 64-bit order:
through the exact Integer observations of its sides. Equal observations are
the same value, by `uint64_equal_of_to_integer` or the `int64` twin.

`squeeze` is the step a loop takes at its exit: `a <= b` and `not a < b`
leave `a == b`. A negated order is read as the order it is, `b <= a`.

`shifted` uses an equality as a premise. `j == i + 1` gives
`to_integer(j) == to_integer(i) + 1` once `i + 1` is known not to wrap,
which `i < n` shows.

`a_uint64_equality_that_does_not_follow_is_not_arithmetic.md` leaves out a
premise.

```click
theorem squeeze(a: uint64, b: uint64) {
    requires a <= b;
    requires not a < b;
    ensures a == b by {
        arithmetic() using { a <= b; not a < b; }
    }
}

theorem shifted(i: uint64, j: uint64, n: uint64) {
    requires j == i + 1u64;
    requires i < n;
    ensures j - 1u64 == i by {
        arithmetic() using { j == i + 1u64; i < n; }
    }
}

theorem signed(a: int64, b: int64) {
    requires a <= b;
    requires b <= a;
    ensures a == b by {
        arithmetic() using { a <= b; b <= a; }
    }
}
```

```expect
pass
```
