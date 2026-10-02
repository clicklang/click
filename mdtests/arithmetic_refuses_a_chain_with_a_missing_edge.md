# arithmetic refuses a chain with a missing edge

The listed premises skip the edge from `a` to `b`, so their sum is not the goal.

```click
theorem broken(x: int32, a: int32, b: int32, c: int32) {
    requires x < a;
    requires b <= c;
    requires c <= 4;
    ensures x < 4 by { arithmetic() using { x < a; b <= c; c <= 4; } }
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
