# A specification quotient needs no divisor premise

Specification `/` and `%` are total. A zero divisor leaves the kernel's
opaque quotient: a fixed value that nothing relates to anything but itself.
So a specification may divide by a divisor that can be zero, with no
`requires` that it is not, and a pure function may divide without a guard.
Signed `MIN / -1` overflows its format, so it still owes its no-overflow
condition, as `+`, `-` and `*` do; `defined(a / b)` still states C's
definedness, including the nonzero divisor
(`mdtests/division_definedness_is_ordinary_propositions.md`).

```click
function mean(total: uint64, count: uint64) -> uint64 {
    total / count
}

theorem a_stated_quotient_needs_no_divisor_premise(a: uint32, b: uint32) {
    ensures a / b == a / b;
    ensures a % b == a % b;
}

theorem a_quotient_by_zero_is_itself(a: uint64) {
    ensures a / 0u64 == a / 0u64;
    ensures a % 0u64 == a % 0u64;
}

theorem a_dividing_function_unfolds_without_a_premise(total: uint64, count: uint64) {
    ensures mean(total, count) == total / count by {
        unfold(mean(total, count));
        solve();
    }
}

theorem a_signed_quotient_needs_only_its_overflow_exclusion(a: int32, b: int32) {
    requires a != -2147483648 or b != -1;
    ensures a / b == a / b;
    ensures a % b == a % b;
}
```

```expect
pass
```
