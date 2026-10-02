# A negative chunk subtraction changes the signed remainder

```click
theorem consume_chunk(n: int32) {
    requires 0 <= n;
    ensures (n - 4) % 4 == n % 4 by { normalize() using { 0 <= n; } }
}
```

```expect
fail: normalize using
```
