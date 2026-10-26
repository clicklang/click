# An unsigned mask refusal does not blame signed overflow

The bitwise mask is total. A bounded arithmetic miss must report insufficient
listed premises rather than suggesting an int32 overflow obligation. The goal
does not follow: the mask may be `1u32`.

```click
theorem masked(units: uint32) {
    requires (units & 1u32) <= 1u32;
    ensures (units & 1u32) < 1u32 by {
        solve() using { (units & 1u32) <= 1u32; };
    }
}
```

```expect
fail: exactly the listed premises were insufficient
```
