# invalid mathematical Integer certificate

```click
theorem arithmetic_certificate_false(x: Integer) {
    ensures x > x + 1 by {
        solve() using {  };
    }
}

theorem integer_constant_certificate_false(x: Integer) {
    ensures 1 == 0 by {
        solve() using {  };
    }
}
```

```expect
fail: solve
```
