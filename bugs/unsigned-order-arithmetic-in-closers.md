# `arithmetic() using` does not use the unsigned order lemmas

## Violated invariant

A true unsigned order fact that follows from cited unsigned facts by
ordinary, non-wrapping arithmetic should close the way its signed
counterpart does. Click spells `a <u b` as the signed order
`(a ^ 2^31) < (b ^ 2^31)`.

`simp` and the loop closer close a goal that is one `uint32` lemma away
from an exact fact (`mdtests/simp_closes_single_unsigned_steps.md`).
`arithmetic() using { … }` does not: it plans one arithmetic certificate
over the listed premises and treats each flipped value as an opaque atom,
so `x - 1u32 < x` from `x > 0u32` is refused.

`arithmetic() using` is one proof step with one certificate, while a
lemma application is an `apply` step, so using the lemmas there means
either an unsigned form of the arithmetic certificate or letting the
tactic record a different step than the one written.

## Intended regression

A theorem-level mdtest closing `x - 1u32 < x` from `x > 0u32`,
`x + 1u32 <= 4u32` from `x < 4u32`, and `1u32 < x` from `x > 1u32` by
`arithmetic() using` with the premise listed. A negative with the premise
omitted is refused.

## Acceptance criteria

- `arithmetic() using` closes the three shapes with a certificate the
  kernel checks, and its expansion verifies.
- Wrapping cases stay refused.
- Work stays linear in the cited premises.
