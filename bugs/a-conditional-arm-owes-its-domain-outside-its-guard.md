# A conditional arm owes its evaluation domain outside its guard

Soundness: incomplete. A defined conditional is refused; nothing false is
accepted.

A specification `if` lowers both arms whatever its condition, and each arm's
evaluation obligations are owed unconditionally. A guarded partial operation,
the usual way to make a pure function total, therefore still owes its domain
where the guard excludes it. `implies` and `or` already scope their right
side's obligations under the left (`lower_spec_disjunction_at_state_in` in
`src/kernel/spec.rs`); `evaluate_spec_if_paths_in`, and its Integer and
algebraic forms, do not. A definition whose zero divisor the guard excludes is
accepted, but every `unfold` of it is refused.

## Reproduction

```click
function q(a: uint64, d: uint64) -> uint64 {
    if d != 0u64 { a / d } else { 0u64 }
}

theorem t(a: uint64, d: uint64) {
    ensures q(a, d) == q(a, d) by {
        unfold(q(a, d));
        solve();
    }
}
```

Refused at the `unfold`: "it denotes a value only where 1 condition of its
evaluation holds ... not established: `d != 0u64`". The written proposition
`(if d != 0u64 { a / d } else { 0u64 }) <= a` is refused the same way.

## Acceptance

- The reproduction verifies; an arm's obligation is owed only where its guard
  selects it (`d != 0 implies ...` for the then arm, `d != 0 or ...` for the
  else arm), for scalar, Integer, and algebraic conditionals.
- An unguarded division in an arm is still refused (`if d == 0u64 { a / d }`).
- A total `format::decimal_digit` (`'0'` past the last digit) unfolds, so the
  `format::decimal_digit_*` theorems pass the library entry point.
