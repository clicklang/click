# A reversed quotient guard does not bound two negative factors

```click
theorem upper(x: int32, y: int32) {
    requires x < 0;
    requires y < -1;
    requires x <= 2147483647 / y;
    ensures to_integer(x) * to_integer(y) <= 2147483647 by {
        close() using { x < 0; y < -1; x <= 2147483647 / y; };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
