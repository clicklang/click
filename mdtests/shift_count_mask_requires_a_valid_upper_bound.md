# A shift-count mask cannot be removed at the first invalid count

```click
theorem shift_count_mask(s: int32) {
    requires s >= 0;
    requires s <= 32;
    ensures (s & 31) == s by known();
}
```

```expect
fail: `known` requires the current goal as an available semantic fact
```
