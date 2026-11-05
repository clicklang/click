# A conditional arm owes its domain only where its guard selects it

An `if` evaluates one arm, so an arm's evaluation domain is owed only where
the condition selects it, as the right side of `implies` and `or` is. A
division guarded by a nonzero divisor makes a pure function total: its
definition unfolds without a premise, and a stated conditional needs none.
An Integer `if` scopes its arms the same way.

```click
function quotient_or_zero(a: uint64, d: uint64) -> uint64 {
    if d != 0u64 { a / d } else { 0u64 }
}

function zero_or_quotient(a: uint64, d: uint64) -> uint64 {
    if d == 0u64 { 0u64 } else { a / d }
}

theorem unfolds_without_a_divisor_premise(a: uint64, d: uint64) {
    ensures quotient_or_zero(a, d) == quotient_or_zero(a, d) by {
        unfold(quotient_or_zero(a, d));
        solve();
    }
}

theorem the_else_arm_is_guarded_too(a: uint64, d: uint64) {
    ensures zero_or_quotient(a, d) == zero_or_quotient(a, d) by {
        unfold(zero_or_quotient(a, d));
        solve();
    }
}

theorem a_stated_conditional_needs_no_premise(a: uint64, d: uint64) {
    ensures (if d != 0u64 { a / d } else { 0u64 }) == (if d != 0u64 { a / d } else { 0u64 }) by {
        solve();
    }
}

theorem an_integer_conditional(a: Integer, d: Integer) {
    ensures (if d != 0 { truncating_quotient(a, d) } else { 0 }) == (if d != 0 { truncating_quotient(a, d) } else { 0 }) by {
        solve();
    }
}
```

```expect
pass
```
