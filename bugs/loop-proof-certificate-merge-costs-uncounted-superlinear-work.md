# A loop proof's certificate merge costs uncounted work that grows faster than the proof

## Violated invariant

A proof written with explicit simple tactics verifies in work approximately
linear in its source, and that work is counted
(`docs/internals/verification-efficiency.md`). After the last leaf of a loop
`preserve` body with many case splits, two steps of the proof layer copy each
path's certificate and charge no deterministic work:

1. `merge_path_aligned_certificates_with_match_policy`
   (`src/surface/proof/execution_planning/context.rs`) recurses once per case
   level. At each level it compares every path's prefix and copies every
   path's remaining tactics (`to_proof_tactics()` and `to_vec()`), so a
   path's tactics are copied once per level of the case tree above it.
2. `certified_loop_exit_transitions_with_proven_phases`
   (`src/surface/proof/execution_planning/transition_certification.rs`)
   clones each exit's propositions and transitions.

Measured with a frame-pointer release build under `perf` on a synthetic loop
whose `preserve` body is a balanced tree of proof `if`s over one C `break`
(`loop_with_break_exits` in `src/surface/tests/scaling_tests.rs`): from 512
to 2048 exits, counted work grows 4 times and the certificate merge's cycles
about 10 times (0.52G to 5.5G). A third step of the same kind,
`Proof::path_certificate` re-reading the whole proof history at every case
split, grew 22 times and is fixed (each proof node now remembers its lineage).

On the rbtree insert frontier (99 exits, about 10,000 proof lines) the work
after the last leaf shows up as 17.9G of 138G cycles under
`certified_loop_exit_transitions_with_proven_phases` and 8.9G under the
certificate merge (whether one contains the other was not checked), none of
it in counted work.

## Intended regression

Extend `loop_break_exit_join_work_is_near_linear_in_the_exits` once the merge
charges what it copies: counted work of the merge near linear in the exits
times the path length at several sizes, failing on the copy-per-level form.

## Acceptance criteria

- Merging path-aligned certificates copies each tactic a bounded number of
  times, independent of the depth of the case tree, and charges it.
- The exit transitions are built without cloning each exit's whole fact list
  more than once, and that work is charged.
- The certificates produced are unchanged: `click expand` and `click audit`
  agree with `click verify` on the existing loop fixtures.
