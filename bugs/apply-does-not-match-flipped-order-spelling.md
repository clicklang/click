# `apply` closes `0 <= e` but not the same claim spelled `e >= 0`

## Violated invariant

`a <= b` and `b >= a` are one proposition. The kernel's affine normalizer
(`integer_affine_claim`) treats both spellings as the same claim, and `simp`
closes either. The standard-library theorem `uint32_to_integer_bounds(value)`
states `0 <= to_integer(value)`; applying it to a goal spelled
`to_integer(x) >= 0` leaves the goal open, while the goal spelled
`0 <= to_integer(x)` closes at once. The surface's theorem-conclusion
matching in `apply` (`src/surface/proof/fixed_state_proofs/theorem_application.rs`)
compares the instantiated conclusion against the goal by spelling rather than
by the normalized order claim.

## Reproduction

```click
theorem t(x: uint32) {
    ensures to_integer(x) >= 0 by { apply(uint32_to_integer_bounds(x)); }
}
```

Observed on 2026-10-07:

```text
proof error:
  checked pure script for `t.ensures_0` ended with its goal still open

goal: to_integer(x) >= 0
```

The same theorem with `ensures 0 <= to_integer(x)` verifies.

## Intended regression

Both spellings as positive mdtests, and the same pair for a strict order
(`<` against `>`), each closed by one `apply`.

## Acceptance criteria

- `apply` recognizes a theorem conclusion as closing the goal when the two
  are the same order claim under the normalization `simp` already uses:
  swapped sides with the mirrored comparison, for `<=`, `>=`, `<`, and `>`,
  over machine and `Integer` operands.
- `scripts/check.sh` passes.
