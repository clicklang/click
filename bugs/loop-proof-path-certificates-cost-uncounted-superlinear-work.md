# A loop proof's path certificates cost uncounted work that grows faster than the proof

## Violated invariant

A proof written with explicit simple tactics verifies in work approximately
linear in its source, and that work is counted
(`docs/internals/verification-efficiency.md`). In a loop `preserve` body with
many case splits, three steps of the proof layer rebuild or copy a path's
whole certificate, none charges deterministic work, and one is quadratic in
the number of paths:

1. `Proof::path_certificate`
   (`src/surface/proof/proof_object/provenance.rs`) walks the proof's whole
   node history from the current node to the root and clones every step on
   the focused path. `split_preservation_case`
   (`src/surface/proof/proof_object/execution_statements.rs`) calls it at
   every proof-level `if` only to read the number of steps, and
   `loop_planning.rs` calls it once per finished leaf. The history holds the
   sibling arms' steps too, so each call is linear in everything checked so
   far and the calls together are quadratic.
2. `merge_path_aligned_certificates_with_match_policy`
   (`src/surface/proof/execution_planning/context.rs`) recurses once per case
   level, and at each level compares every path's prefix and copies every
   path's remaining tactics, so a path's tactics are copied once per level of
   the case tree above it.
3. `certified_loop_exit_transitions_with_proven_phases`
   (`src/surface/proof/execution_planning/transition_certification.rs`)
   clones each exit's propositions and transitions.

Measured on `a08e0fe8a` with the two pairwise exit comparisons already
replaced (the exit disjunction and the exit dedup), on a synthetic loop whose
`preserve` body is a balanced tree of proof `if`s over one C `break`
(`loop_with_break_exits` in `src/surface/tests/scaling_tests.rs`), with a
frame-pointer release build under `perf`:

| exits | counted work | CPU cycles | in `path_certificate` |
| --- | --- | --- | --- |
| 512 | 0.85M | 11.8G | 0.48G |
| 2048 | 3.44M | 68.6G | 10.7G |

Counted work quadruples; cycles grow 5.8 times; `path_certificate` grows 22
times and the certificate merge about 10 times. The 512-exit row was taken
before the two pairwise fixes, which do not touch these functions.

On the rbtree insert frontier (99 exits, about 10,000 proof lines) the work
after the last leaf shows up as 17.9G of 138G cycles under
`certified_loop_exit_transitions_with_proven_phases` and 8.9G under the
certificate merge (whether one contains the other was not checked). The
kernel's own exit proof is about 3G. The `loop` tactic's counted work does
not reflect it: the last sixteen leaves added 1.08M units and the certificate
work with them.

## Intended regression

A deterministic scaling test over `loop_with_break_exits` at several sizes
that charges and bounds the certificate work: the number of history nodes
`path_certificate` visits and the number of tactics the merge copies, each
near linear in the exits times the path length. The test must fail on the
current walk-to-root and copy-per-level forms.

## Acceptance criteria

- A proof-level case split reads its path's step count without rebuilding
  the certificate, and a leaf's certificate is built from that path's own
  nodes rather than by filtering the whole history.
- Merging path-aligned certificates copies each tactic a bounded number of
  times, independent of the depth of the case tree.
- Every one of these steps charges deterministic work proportional to what
  it reads, so a budget verdict and a scaling measurement see it.
- The certificates produced are unchanged: `click expand` and `click audit`
  agree with `click verify` on the existing loop fixtures.
