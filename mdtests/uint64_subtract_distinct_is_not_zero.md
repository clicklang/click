# Distinct full-width unsigned operands do not cancel

```click
theorem subtract_distinct(n: uint64, m: uint64) {
    ensures n - m == 0u64 by close();
}
```

```expect
fail: could not establish `(to_integer(n) - to_integer(m)) == to_integer(0u64)`
```
