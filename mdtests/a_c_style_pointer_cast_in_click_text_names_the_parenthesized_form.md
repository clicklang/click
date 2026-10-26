# A C-style pointer cast in Click text names the parenthesized `as` form

A pointer cast target is parenthesized, `e as (uint8 *)`, so the refusal of
the C spelling names that form.

```click
theorem same_bytes(p: int32*) {
    ensures (uint8 *) p == (uint8 *) p;
}
```

```expect
fail: a Click cast is written after its operand: write `e as (uint8 *)`, not `(uint8 *) e`
```
