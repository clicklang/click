# Measure induction over a full-width count

The measure and its smaller arguments keep their unsigned 64-bit type.
The induction hypothesis retains the theorem's other requirements.

```click
theorem full_width_induction(n: uint64, limit: uint64) {
    requires n <= limit;
    ensures n <= limit by {
        induct(n) as ih;
        if n <= 0u64 {
            assumption();
        } else {
            have 0u64 < n by simp();
            have to_integer(n - 1u64) < to_integer(n) by arithmetic() using { 0u64 < n; };
            have to_integer(n - 1u64) <= to_integer(limit) by arithmetic() using { 0u64 < n; n <= limit; };
            apply(ih(n - 1u64)) using {
                to_integer(n - 1u64) < to_integer(n);
                to_integer(n - 1u64) <= to_integer(limit);
            };
            assumption();
        }
    }
}
```

```expect
pass
```
