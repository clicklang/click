# A uint64 sum that may wrap is not arithmetic

`i + 1 < length` does not give `i + 2 <= length` for `uint64` values on its
own: `i` may be the largest value, where `i + 1` wraps to zero and `i + 2`
to one. `arithmetic` proves a 64-bit goal through Integer observations, and
a sum is the sum of its operands' observations only when it does not wrap.
The premises here do not bound `i`, so the step is refused, naming the sum.

`a_size_t_loop_stepping_by_two_closes_with_arithmetic.md` lists the bounds.

```click
theorem step_two(i: uint64, length: uint64) {
    requires to_integer(i + 1u64) < to_integer(length);
    ensures to_integer(i + 2u64) <= to_integer(length) by {
        arithmetic() using { to_integer(i + 1u64) < to_integer(length); };
    }
}
```

```expect
fail: stays within uint64
```
