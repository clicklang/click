# `apply ... using` requires an exact premise

`x > 0` implies `x >= 0`, but `apply ... using` is a simple tactic and does
not search for that derivation. Each listed premise must be present as an
exact pure fact. The bare `apply(needs_nonnegative(x))` does not prove it
either; a proof states it first with `have`
([`apply_cites_a_premise_stated_first.md`](apply_cites_a_premise_stated_first.md)).

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        assumption();
    }
}

theorem positive_is_not_an_exact_premise(x: int32) {
    requires x > 0;

    ensures x >= 0 by {
        apply(needs_nonnegative(x)) using { x >= 0; };
        assumption();
    }
}
```

```expect
fail: requires an unavailable exact premise: `x >= 0`
```
