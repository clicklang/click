# A C-style cast in Click text names the `as` form

Click writes a cast after its operand, `e as T`
(`docs/reference/language/index.md`, Casts). The C spelling `(T) e` is
refused in Click text with the replacement spelled out; C source keeps its
own casts.

```click
theorem narrow(x: int64) {
    requires 0 <= x and x <= 10;
    ensures (int32) x <= 10;
}
```

```expect
fail: a Click cast is written after its operand: write `e as int32`, not `(int32) e`
```
