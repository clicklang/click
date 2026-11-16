# An arithmetic certificate cites operation and excluded bounds

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem shifted_guard(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 4294967296u64 <= v by {
        solve() using { to_integer((v >> 32)) != 0; };
    };
}
```

```expect
pass
```
