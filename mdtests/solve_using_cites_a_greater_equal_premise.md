# `close() using` cites a greater-or-equal premise

`close() using` indexes each cited signed comparison under both spellings, so a
premise written `x >= 0` also closes the goal spelled `0 <= x`. This catches a
conditional normalizer that drops the mirrored form of a cited `>=` condition.

```click quick-solve
theorem greater_equal_premise_closes_mirrored_goal(x: int32) {
    requires x >= 0;
    ensures 0 <= x by {
        close() using { x >= 0; };
    }
}
```

```expect
pass
```
