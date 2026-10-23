# A resource fact guard of exact observations cannot read past its range

A guard of exact observations bounds the index as its native comparison
does, so `to_integer(k) < to_integer(len + 2u64)` includes `p[len + 1u64]`,
one past the owned `p[0..len + 1u64]`, and the read is refused. The accepted
guard is `resource_fact_guard_of_exact_observations_bounds_its_index.md`.

```click
resource too_wide(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551614u64;
    fact forall (k: uint64) {
        0u64 <= k and to_integer(k) < to_integer(len + 2u64) implies defined(p[k])
    };
}
```

```expect
fail: resource `too_wide` fact reads `p[k]` without a covering contained memory resource with current read authority
```
