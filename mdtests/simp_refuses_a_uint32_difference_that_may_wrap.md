# simp refuses a uint32 difference that may wrap

`3 - x <u 4 - x` is false at `x == 4`, where `3 - x` wraps to `UINT_MAX`.
The descent lemma requires `x <u 4`; `x <=u 4` is not that fact, so `simp`
leaves the goal open.

```click
theorem difference_that_may_wrap(x: uint32) {
    requires x <= 4u32;
    ensures (0u32 - x) + 3u32 < (0u32 - x) + 4u32 by simp;
}
```

```expect
fail: could not establish `((0u32 - x) + 3u32) < ((0u32 - x) + 4u32)`
```
