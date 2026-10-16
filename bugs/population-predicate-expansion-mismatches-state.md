# A produced-population predicate fails after proof expansion

Priority: P2.

Soundness: incomplete. The original checked proof passes, but its generated
explicit proof fails to close the same postcondition. This is a disagreement
between verification and expansion, not a demonstrated false accepted proof.

## Reproduction

Use the complete existing fixture
`mdtests/produced_population_count_in_ensured_predicate.md`, including its
unchanged C functions and contracts. Ordinary verification succeeds:

```sh
cargo run --bin click -- verify mdtests/produced_population_count_in_ensured_predicate.md
```

The selected complete-claim audit fails:

```sh
cargo run --bin click -- audit --claim produce_population.contract mdtests/produced_population_count_in_ensured_predicate.md
```

The `produce_population` contract owns authority for `slot(owner)`, explicitly
requires its entry count to be zero, and produces `amount` members after
writing `owner->capacity = amount`. Its `valid_capacity(owner)` postcondition
states that this field equals the current family count. The positive branch
folds the population before returning; the zero branch proves `amount == 0`.

The generated proof first completes a `have valid_capacity(owner)` scope,
then fails at path 0, tactic 9: `assumption` cannot establish
`valid_capacity(owner)`. The diagnostic's lowered goal is
`amount == <unnamed A> + amount`, even though the recent-premise list includes
`valid_capacity(owner)`. The trace includes the entry counter's zero equality,
so this is not evidence that the entry-zero premise disappeared. The retained proof must preserve the
predicate's state arguments as well as its spelling. Moving the generated
`unfold(valid_capacity)` inside the `have` scope still fails at the following
`assumption`, now with the opaque predicate as the goal; unfold scope alone
does not reduce this mismatch.

This failure also appears in the October 16 nightly expansion audit at
`d86757df2` and reproduces while repairing the audit on the `0dd554178` base.
It also reproduces after updating those repairs to `358eb9747`; the ordinary
proof still passes. It is independent of the pointer-comparison repairs.

## Acceptance

- Preserve the checked count and predicate-state dependencies when
  serializing and materializing the successful `have`; its completed fact
  must denote the same predicate instance the claim needs.
- Pass the original fixture's complete audit, including the helper and its
  modular caller, fresh rewritten checking, and retained checking.
- Keep the explicit empty-entry requirement: authority ownership alone must
  not imply a zero population.
- Reject an incorrect produced count, an incorrect capacity, or removal of
  the required authority. Keep existing work and timing limits.
