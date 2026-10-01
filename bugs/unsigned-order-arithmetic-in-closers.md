# `simp` and `arithmetic()` treat sign-bit-flipped unsigned values as opaque

## Violated invariant

A true unsigned order fact that follows from cited unsigned facts by
ordinary, non-wrapping arithmetic should close the way its signed
counterpart does. Click spells `a <u b` as the signed order
`(a ^ 2^31) < (b ^ 2^31)`, and `simp` and `arithmetic() using { … }` treat
each flipped value as an opaque atom. PR #54 composes chains of facts over
the same atoms, but nothing relates the flip of `x + 1` or `x - 1` to the
flip of `x`. So none of these close:

- `x - 1u32 < x` from `x > 0u32`;
- `x + 1u32 <= 4u32` from `x < 4u32`, even though the guard also files the
  signed pair `0 <= x`, `x < 4`, because a surface premise on a `uint32`
  cannot be spelled as that signed fact;
- a goal `1u < x` from the fact `x > 1u`, the same comparison written the
  other way round;
- the descent of an unsigned measure such as `n - x`:
  `(n - x) - 1 <u n - x` from `x <u n`, which needs `n - x` treated as a
  subtraction that does not wrap once `x <=u n` is known.

Since unsigned `decreases` measures landed, every true unsigned loop measure
over a counter fails at this point.

## Intended regression

These mdtests pin the gap today; each should change to `pass` with no change
to its C source, and to its proof beyond explicit simple tactics if needed:

- `mdtests/an_unsigned_count_down_loop_owes_an_unsigned_descent.md`
  (`while (x > 0u) x--;`, `decreases x`)
- `mdtests/an_unsigned_loop_to_a_variable_bound_owes_an_unsigned_descent.md`
  (`while (x < n) x++;`, `decreases n - x`)
- `mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`
  (invariant `x <= 4u32`, `decreases 4 - x`)
- `mdtests/an_unsigned_loop_counter_store_is_bounded_by_a_variable_guard.md`
  (invariant `x <= n`, `decreases 4 - x`)

Plus a theorem-level mdtest covering the three single-step shapes above, by
`simp()` and by `arithmetic() using`. The negatives
`mdtests/an_unsigned_measure_that_grows_is_refused.md` and
`mdtests/an_unsigned_measure_that_wraps_upward_is_refused.md` must stay
refused.

## Acceptance criteria

- `a ± c` with a constant `c` relates to `a` through the flip whenever the
  cited facts rule out wraparound (for example `a >u 0` for `a - 1`, or
  `a <u k` for `a + 1`), with a certificate the kernel checks.
- `a >u b` and `b <u a` are the same fact to `simp`, `arithmetic` and the
  loop closer.
- An unsigned subtraction `n - x` under `x <=u n` is read as the
  non-wrapping difference.
- Wrapping cases stay refused: `3 - x <u 4 - x` does not close at `x == 4`.
- Work stays linear in the cited premises; nothing scans ambient facts.
