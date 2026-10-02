# arithmetic refuses an unsigned step from another value's premise

The listed premise bounds `y`, not `x`, so no lemma about `x - 1` applies
and the goal stays open.

```click
theorem wrong_premise(x: uint32, y: uint32) {
    requires x > 0u32;
    requires y > 0u32;
    ensures x - 1u32 < x by { arithmetic() using { y > 0u32; } }
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
