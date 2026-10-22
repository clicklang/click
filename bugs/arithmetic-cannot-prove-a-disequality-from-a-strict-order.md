# `arithmetic` cannot prove a disequality from a strict order

Soundness: no soundness impact. A true linear claim is refused and nothing
false is accepted.

`arithmetic()` proves linear comparisons from its listed premises, and `auto`
runs the same Integer solver, so a disequality that follows linearly from
the premises should close: `k < j` gives `k != j`, because `k == j` together
with `k < j` is a linear contradiction. Today no closer proves it, for
machine or Integer operands:

```click
theorem native_lt_neq(k: int32, j: int32) {
    requires k < j;
    ensures k != j by auto();
}
```

- `auto()` on `int32` or on `Integer` operands: `simp` failed ... could not
  establish `k != j`.
- `arithmetic() using { k < j; }` on `Integer` operands: `arithmetic`
  requires a supported signed int32 comparison or equality goal.
- `arithmetic() using { k < j; }` on `int32` operands: current goal does
  not follow from exactly the listed arithmetic premises.

The Integer affine fragment reads a `!=` only between constants
(`integer_affine_claim_with_context` in `src/kernel/proof/integer_arithmetic.rs`:
"Disequality is outside this fragment, except for constants"). A refutation
of a `!=` goal needs only its negation, the equality `k == j`, which the
fragment already reads. Before Integer-default arithmetic, proofs used the
`int32_less_than_implies_not_equal` bridge lemma for this. Migrated proofs
(`mdtests/bubble_sort3_two_pass_sorted.md`) now state a stronger order the
next step accepts instead.

## Reproduction

From the repository root:

```sh
click verify bugs/arithmetic-cannot-prove-a-disequality-from-a-strict-order.click
```

The companion file holds the four theorems above: `auto()` and
`arithmetic() using { k < j; }`, each on `int32` and on `Integer` operands.
Each is refused.

## Acceptance criteria

- `arithmetic()` proves `a != b` when its listed premises refute `a == b`
  linearly, for machine and Integer operands, and checks a certificate for
  it. `auto` closes the same goals from the facts in scope.
- A regression covers `k < j` giving `k != j` on `int32` and on `Integer`,
  and a refused disequality whose premises do not exclude equality.
