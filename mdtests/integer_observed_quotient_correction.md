# Observed quotient correction

```click
theorem observed_quotient_correction(q: int64, quotient: Integer) {
    requires defined(q + 1i64);
    requires to_integer(q) == quotient;
    ensures to_integer(q + 1i64) == quotient + 1 by {
        apply(int64_add_to_integer(q, 1i64));
        rewrite(to_integer(q + 1i64) == to_integer(q) + 1);
        rewrite(to_integer(q) == quotient);
        simp();
    }
}
```

```expect
pass
```
