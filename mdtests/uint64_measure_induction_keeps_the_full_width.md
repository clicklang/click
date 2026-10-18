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
            have n - 1u64 < n by arithmetic() using { 0u64 < n; };
            have n - 1u64 <= limit by arithmetic() using { 0u64 < n; n <= limit; };
            apply(ih(n - 1u64)) using {
                n - 1u64 < n;
                n - 1u64 <= limit;
            };
            assumption();
        }
    }
}
```

```expect
pass
```
