# A conditional arm still owes a domain its guard does not give

Scoping an arm under its guard does not drop its obligation: the arm selected
by `d == 0` divides by zero, so the conditional is refused where it is stated.

```click
theorem unguarded(a: uint64, d: uint64) {
    ensures (if d == 0u64 { a / d } else { 0u64 }) == 0u64 by {
        solve();
    }
}
```

```expect
fail: it denotes a value only where 1 condition of its evaluation holds
```
