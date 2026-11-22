# A shift-count mask cannot be removed at the first invalid count

```click
theorem shift_count_mask(s: int32) {
    requires s >= 0;
    requires s <= 32;
    ensures (s & 31) == s by {
        normalize() using { s >= 0; s <= 32; };
    }
}
```

```expect
fail: goal did not normalize to true using the listed conditions
```
