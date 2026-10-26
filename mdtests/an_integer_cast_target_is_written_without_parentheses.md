# An integer cast target is written without parentheses

Only a pointer cast target is parenthesized; an integer target is bare,
`x as int32`.

```click
theorem narrow(x: int64) {
    requires 0 <= x and x <= 10;
    ensures x as (int32) <= 10;
}
```

```expect
fail: an integer cast target is written without parentheses: `e as uint32`; only a pointer target is parenthesized, `e as (uint8 *)`
```
