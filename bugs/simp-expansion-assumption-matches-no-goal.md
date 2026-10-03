# Expanded `simp` emits an `assumption` that matches no goal

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the
same claim (`click audit` checks this).

Tactics written after `execute()` are deferred and run against the function's
claims. A deferred `witness` (or `intro`) opens the claim's own proof. A
following `simp()` expands to the whole claim's certificate,
`have <claim> by { ... }; assumption();`, and when the expansion is checked that `assumption`
matches no goal.

The `intro` case is fixed: `simp()` now records only the steps it adds to
the proof the `intro`s opened, and deferred `normalize`, `assumption` and
arithmetic closers continue that proof
(`post_execution_closer_continues_the_proof_intros_opened`).

The `witness` case remains, in `mdtests/cstr_stdlib.md`
(`plain_cstr.exposes_ghost_length`: `unfold(cstr); let ... satisfy ...;
witness(len = found_len); simp();`). Applying the same change to
`witness`-opened proofs makes that fixture audit clean but breaks two
properties:

- `post_execution_choose_and_witness_share_the_retained_outcome_proof`
  requires that changing the witness invalidates the expanded proof. With
  the shorter expansion, a deferred `assumption` that does not close the
  opened proof has to fall back to the claim-level reading, which can close
  the claim from ambient facts and ignore the witness.
- `bounded_range_witness_closes_on_the_checked_outcome_scope` needs that
  claim-level fallback: its `assumption` does not close the opened proof's
  goal, a conjunction.

So the fix needs a closer that continues a `witness`-opened proof without
silently dropping the witness.

## Intended regression

Reduce `mdtests/cstr_stdlib.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
