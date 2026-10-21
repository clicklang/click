# `auto` refuses a quotient bound past the floor

`4294967296 / 1000` is `4294967`, so a `v` of at least `4294967296` gives
`4294967 <= v / 1000`, and not one more. The operand bound is the floor of
the division; it does not round up.

```click
theorem quotient_past_the_floor(v: uint64) {
    requires 4294967296u64 <= v;
    ensures 4294968u64 <= v / 1000u64 by { auto(); };
}
```

```expect
fail: could not establish `4294968u64 <= (v / 1000u64)`
```
