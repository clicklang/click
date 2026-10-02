# Unsigned order arithmetic closes only by named lemmas

## Violated invariant

A true unsigned order fact that follows from cited unsigned facts by
ordinary, non-wrapping arithmetic should close the way its signed
counterpart does. Click spells `a <u b` as the signed order
`(a ^ 2^31) < (b ^ 2^31)`.

The `uint32_*` lemmas in the prelude state the single steps, and a proof
that applies them verifies an unsigned count-down or count-up loop
(`mdtests/an_unsigned_count_down_loop_owes_an_unsigned_descent.md`,
`mdtests/an_unsigned_loop_to_a_variable_bound_owes_an_unsigned_descent.md`).
Two things remain.

**A measure `c - x` over a constant has no lemma that matches it.** The
loop evaluates `4 - (x + 1)` and `4 - x` to the affine forms
`(0 - x) + 3` and `(0 - x) + 4`. The predecessor lemma applied to `4 - x`
concludes `(4 - x) - 1 <u 4 - x`, a different spelling of the same
values, and no explicit step relates the two: `normalize`, `simp` and
`arithmetic` all refuse `(4u32 - e) - 1u32 == (0u32 - e) + 3u32`, and an
instantiated lemma does not fold `((0 - e) + 3) + 1` to `(0 - e) + 4`.
So these stay refused:

- `mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`
  (invariant `x <= 4u32`, `decreases 4 - x`)
- `mdtests/an_unsigned_loop_counter_store_is_bounded_by_a_variable_guard.md`
  (invariant `x <= n`, `decreases 4 - x`)

Their invariant members close with `uint32_increment_upper_bound`; only
the decrease member is stuck.

**`simp` and `arithmetic() using { … }` do not use the lemmas.** They treat
each flipped value as an opaque atom, so `x - 1u32 < x` from `x > 0u32`
needs the lemma applied by name.

## Intended regression

The two fixtures above change to `pass` with no change to their C source.
The negatives `mdtests/an_unsigned_measure_that_grows_is_refused.md` and
`mdtests/an_unsigned_measure_that_wraps_upward_is_refused.md` must stay
refused.

## Acceptance criteria

- Two spellings of one uint32 value that differ by reassociating constants
  are related by an explicit step with a certificate the kernel checks.
- An unsigned subtraction `c - x` under `x <=u c` is read as the
  non-wrapping difference.
- Wrapping cases stay refused: `3 - x <u 4 - x` does not close at `x == 4`.
- Work stays linear in the cited premises; nothing scans ambient facts.
