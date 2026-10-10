# assumption names the missing side

`assumption()` looks each side of a conjunction up and derives nothing. Here
`x <= 10` follows from `x <= 5` but is not itself a fact, so the step is
refused and names that side. `have x <= 10 by simp;` before it repairs it.

```click
theorem assumption_missing_side(x: int32) {
    requires 0 <= x;
    requires x <= 5;
    ensures 0 <= x and x <= 10 by assumption();
}
```

```expect
fail: `assumption` closes a conjunction when every side is an available fact and a disjunction when one side is; `x <= 10 is true` is not available
```
