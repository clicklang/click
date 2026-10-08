# Distinct full-width unsigned operands do not cancel

```click
theorem subtract_distinct(n: uint64, m: uint64) {
    ensures n - m == 0u64 by { normalize(); }
}
```

```expect
fail: goal did not normalize to true
```
