# `apply using` does not derive an unstated premise

The selected fact `x > 0` implies `x >= 0`, but explicit `apply using`
requires evidence stating the theorem requirement. Bare pure `apply` instead
generates a premise obligation for the driver to solve.

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
        apply(needs_nonnegative(x)) using { x > 0; };
        assumption();
    }
}
```

```expect
fail: required exact fact for theorem `needs_nonnegative` is unavailable
```
