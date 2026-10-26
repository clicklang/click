# An Integer-valued `if` in a theorem verifies

A conditional whose branches are Integers is an Integer: here `n + 1` and
`n`, compared with `n - 1`. Its condition stays a proposition. Lowering keeps
both branches, because the condition is not a literal constant, so the proof
splits on the condition and each case reduces the conditional to its branch
with `solve`, as it would a machine conditional
(`mdtests/an_integer_if_is_reduced_under_a_known_condition.md`).

```click
theorem successor_or_self_exceeds_predecessor(n: Integer, k: int32) {
    ensures (if k > 0 { n + 1 } else { n }) > n - 1 by {
        if k > 0 {
            have (if k > 0 { n + 1 } else { n }) == n + 1 by solve();
            solve();
        } else {
            have (if k > 0 { n + 1 } else { n }) == n by solve();
            solve();
        }
    }
}

theorem equal_branches_are_one_value(x: Integer, y: Integer, c: bool) {
    requires x == y;
    ensures (if c { x } else { y }) == x;
}
```

```expect
pass
```
