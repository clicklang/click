# A `solve() using` miss reports arithmetic's reason

`solve() using` tries arithmetic last over the listed premises. When nothing
closes the goal, its refusal adds arithmetic's own reason: here the one
listed premise, `x == y`, does not give `x <= z`, and the ambient `y <= z`
is not listed.

```click
theorem listed_premises_fall_short(x: int32, y: int32, z: int32) {
    requires x == y;
    requires y <= z;

    ensures x <= z by {
        solve() using {
            x == y;
        };
    }
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
