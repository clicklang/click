# Distributivity arguments retain truncation domains even in a zero product

```click
theorem erased_domain(n: Integer, d: Integer) {
    ensures 0 == 0 by {
        apply(integer_multiply_add(truncating_quotient(n, d), 0, 0));
        simp();
    }
}
```

```expect
fail: could not lower theorem requirements
```
