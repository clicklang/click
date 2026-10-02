# A uint32 predecessor at zero is refused

`x - 1 <u x` is false at `x == 0`, where the predecessor wraps to
`UINT_MAX`. The predecessor lemma requires `0 <u x`, and a proof that does
not have that fact cannot apply it.

```click
theorem predecessor_without_a_guard(x: uint32) {
    ensures x - 1u32 < x by {
        apply(uint32_positive_predecessor_strictly_decreases(x)) using { 0u32 < x; }
    }
}
```

```expect
fail: `apply using` requires an unavailable exact premise: `0u32 < x`
```
