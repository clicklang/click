# `apply` does not prove a missing premise

`apply(theorem(args))` looks each of the theorem's premises up among the
available facts and proves none. Here `x >= 0` follows from `x > 0`, but it is
not an available fact, so the application is a search miss: the refusal says
so and names the `have` that states the premise, after which the application
finds it (`apply_cites_a_premise_stated_first.md`).

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        assumption();
    }
}

theorem positive_premise(x: int32) {
    requires x > 0;

    ensures x >= 0 by {
        apply(needs_nonnegative(x));
        assumption();
    }
}
```

```expect
fail: required exact fact for theorem `needs_nonnegative` is unavailable: requirement 1 `x >= 0` instantiates to x >= 0
  this is a search miss, not a refusal; no available fact states the requirement, and the elided `apply` proves none; if it holds, state it first with `have x >= 0 by { ... }`
```
