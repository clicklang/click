# Single-operation signed interval normalization

```click
theorem shift_interval(x: int32) {
    requires 0 <= x;
    requires x <= 100;
    requires defined(x << 2);
    ensures 0 <= to_integer(x << 2) by {
        close() using { 0 <= x; x <= 100; };
    }
}
```

```expect
pass
```
