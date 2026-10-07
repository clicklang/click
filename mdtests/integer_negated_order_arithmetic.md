# Arithmetic certificates from negated Integer order

```click
theorem negated_lower(n: Integer) {
    requires not (n <= 0);
    ensures 0 <= n by { arithmetic() using { not (n <= 0); } }
}
theorem negated_upper(n: Integer) {
    requires not (0 <= n);
    ensures n <= 0 by { arithmetic() using { not (0 <= n); } }
}
```

```expect
pass
```
