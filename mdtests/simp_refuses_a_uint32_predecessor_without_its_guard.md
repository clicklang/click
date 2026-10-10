# simp refuses a uint32 predecessor without its guard

`x - 1 <u x` is false at `x == 0`, where the predecessor wraps to
`UINT_MAX`. Without the fact `0 <u x` there is no lemma to apply, and `simp`
leaves the goal open.

```click
theorem predecessor_without_a_guard(x: uint32) {
    ensures x - 1u32 < x by simp;
}
```

```expect
fail: could not establish `(x - 1u32) < x`
```
