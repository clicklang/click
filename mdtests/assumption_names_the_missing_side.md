# assumption names the missing side

`assumption()` checks each side modulo known equalities, without searching
for arithmetic consequences. Here
`x <= 10` follows from `x <= 5` but is not itself a fact, so the step is
refused and names that side. `have x <= 10 by simp();` before it repairs it.

```click
theorem assumption_missing_side(x: int32) {
    requires 0 <= x;
    requires x <= 5;
    ensures 0 <= x and x <= 10 by assumption();
}
```

```expect
fail: missing exact fact: x <= 10
```
