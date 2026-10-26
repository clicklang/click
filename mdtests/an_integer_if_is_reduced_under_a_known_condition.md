# An Integer `if` is reduced under a known condition

An Integer conditional is decided by the proof, as a machine one is
(`mdtests/conditional_spec_branch_is_a_proof_step.md`,
`mdtests/normalize_using_decides_conditions_without_substituting.md`):
lowering keeps both branches, and a known condition selects one. The omitted proof
reads `requires limit > 0` to select the first branch of a postcondition,
`normalize() using` decides a cited guard, and `solve` decides one from the
facts.

```c filename=an_integer_if_is_reduced_under_a_known_condition.c
int32 select_when_positive(int32 limit, int32 left, int32 right) {
    return left;
}
```

```click
verifying "an_integer_if_is_reduced_under_a_known_condition.c";

int32 select_when_positive(int32 limit, int32 left, int32 right) {
    requires limit > 0;
    ensures result == (if limit > 0 { left } else { right + 1 });
}

theorem guard_is_decided(x: Integer) {
    requires x == 7;
    ensures (if x == 7 { x + 1 } else { 2 }) == x + 1 by {
        normalize() using { x == 7; };
    }
}

theorem simp_decides_the_condition(x: int32, n: Integer) {
    requires x > 3;
    ensures (if x > 3 { n } else { n - 1 }) == n by solve();
}
```

```expect
pass
```
