# explicit signed int32 arithmetic certificate

```click
theorem signed_int32_certificate_surface(x: int32) {
    requires x <= 1;
    ensures x <= 1 by {
        solve() using { x <= 1; };
    }
}
```

```expect
pass
```
