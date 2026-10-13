# `normalize` leaves an unsigned shift by a folded amount unevaluated

Soundness: not soundness. A closed, true constant goal is refused; nothing
false is accepted.

`normalize()` must evaluate a closed machine-integer expression. After a
`rewrite` replaces a variable with a constant, an unsigned left shift whose
amount is `(0u32 - (uint32)(x >> 59u64)) & 31u32` is left unevaluated, and
the residual goal prints without its `u32` types and with the right side as a
negative number.

Reproduced on master `6f16a4a8`:

```click
theorem cast_shift(x: uint64) {
    requires x == 1753877967969059832u64;
    ensures (182457789u32 << ((0u32 - (uint32)(x >> 59u64)) & 31u32)) == 2684354560u32 by {
        rewrite(x == 1753877967969059832u64);
        normalize();
    }
}
```

```text
`normalize` goal did not normalize to true
goal: 182457789 << (-3 & 31) == -1610612736
```

The same steps prove `((0u32 - (uint32)(x >> 59u64)) & 31u32) == 29u32`,
and `normalize()` proves the shift when every operand is written as a
literal. `simp()` on the residual reports "an internal int32 equality goal
with no Click spelling", and `arithmetic()` treats it as signed, so the folded
mask appears to be retyped as `int32`.

This blocks the PCG client proof in issues/private-static-helper-ownership.md:
the output of `pcg32_random_r` rotates by `(-rot) & 31` (that is,
`(0u32 - rot) & 31u32`), and evaluating it on the seeded state reaches exactly this
residual.

Acceptance:

- The reproduction verifies, and a false right side (`2684354561u32`) is
  still refused.
- A residual goal keeps its unsigned types when printed.
