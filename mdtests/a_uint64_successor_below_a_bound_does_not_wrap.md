# A uint64 successor below a bound does not wrap

`i < length` gives `i + 1 <= length` for `uint64` values with no bound on
`length` stated: `length` is itself at most the largest `uint64`, so `i` is
below that and `i + 1` does not wrap.

`arithmetic` proves a 64-bit goal through Integer observations, and reads
the sum as the sum of its operands' observations once it is shown not to
wrap. It states the type's range for each value written
(`uint64_to_integer_bounds`), which is the fact that shows it here.

`a_uint64_sum_that_may_wrap_is_not_arithmetic.md` has a sum the premises
do not keep in range.

```click
theorem successor(i: uint64, length: uint64) {
    requires i < length;
    ensures i + 1u64 <= length by {
        arithmetic() using { i < length; }
    }
}
```

```expect
pass
```
