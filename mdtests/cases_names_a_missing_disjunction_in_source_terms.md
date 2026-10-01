# `cases` names a missing disjunction in source terms

`cases(P)` splits on a disjunction that is already an available fact. When it
is not, the refusal spells the disjunction in source terms, not as a dump of
the kernel's internal proposition.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        cases(x > 0 or x < 0) { simp(); } { simp(); }
    }
}
```

```expect
fail: `cases` requires its exact disjunction as an available fact: `(x > 0 || x < 0)`
```
