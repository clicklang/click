# explicit mathematical Integer certificate

```click
theorem arithmetic_certificate_success(x: Integer) {
    ensures x + 1 > x by {
        solve() using {  };
    }
}

theorem integer_constant_certificate(x: Integer) {
    ensures 0 == 0 by {
        solve() using {  };
    }
}
```

```expect
pass
```
