# Rounding requires all stated reconstruction and correction premises

```click
theorem incomplete(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by apply(integer_floor_from_remainder(n, d, q, r, value));
}
```

```expect
fail: integer_floor_from_remainder
```
