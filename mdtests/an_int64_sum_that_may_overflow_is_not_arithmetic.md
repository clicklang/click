# An int64 sum that may overflow is not arithmetic

`i <= length` bounds `i` from above only. `i - 1` may then go below the
least `int64`, where the subtraction is undefined, so it has no Integer
observation to reason with. The claim `to_integer(i - 1i64) <= ...` is refused
where it is stated, naming the difference that must not overflow.

`arithmetic_proves_int64_order_goals.md` has the goals that do follow.

```click
theorem predecessor(i: int64, length: int64) {
    requires i <= length;
    ensures to_integer(i - 1i64) <= to_integer(length) by {
        solve() using { i <= length; };
    }
}
```

```expect
fail: not established: `i - 1i64` must not overflow
```
