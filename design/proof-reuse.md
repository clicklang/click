# Proof reuse and case structure

This record preserves the completed proof-consolidation work and the decisions
from the October 2026 review. It is not a backlog or a claim that the current
rbtree corpus is green. Current acceptance belongs to the
[rbtree milestone](../roadmap/rbtree-example.md); current tactics belong to the
[tactic reference](../docs/reference/tactics/index.md).

## R1. Retire superseded increments (process)

Keep a general proof and its distinct regressions. When it subsumes a case
increment, move the increment's mutation controls to the general proof and
delete the increment. Preserve the mutation's intended refusal, rather than
accept a new source-position error. Slow mutation checks belong in nightly.
This rule is also in [Examples](../examples/README.md).

Completed: 22 superseded color-repair sidecars were deleted, removing roughly
29,000 lines. Their 39 distinct C mutations remained covered by the general
proof. Those historical counts measure the consolidation, not today's corpus.

## R2. One general contract per function

Prefer one general contract with proof-case arms, so the common C prefix is
executed once. The general unlink and `rb_erase` contracts replaced 16 case
sidecars with three shared/general sidecars in October 2026. Outcome-dependent
resources distinguish a balanced result from a black-height deficit.
The leaf wrapper remains because the augmented proof consumes its distinct
hole/context interface. Generalization is not grounds to discard a distinct
claim or regression.

The prototype reduced the selected files from 4,815 to 2,793 lines and the
sum of single release runs from 37.7 to 21.1 seconds. These are historical
measurements, not current performance guarantees. Contract intersection was
not needed; it would re-execute the common prefix for each case.

## R3. Recursive specification functions

Bounded smart search may unfold a recursive pure function over a known
constructor and retain explicit checked rewrites for expansion. This is
implemented. It does not make general recursive reasoning complete or
establish that the current rbtree proofs pass.

## R4. Automatic opening and closing of resources

A written `step()` executes a C operation and does not open a folded resource.
The implicit execution tail can select a unique ordinary owned resource that
blocks an access, open one layer and retry. Expansion writes the opening
explicitly. Current orchestration and obligation handling are recorded in
[Proof operations and search](proof-operations-and-search.md).

The review did not pursue automatic opening of recursive named instances or
inventing their new models for refolding. These require model information and
child names that are not predictable from the written operation. Explicit
`unfold` and `fold` retain that control. This is a decision, not unfinished R4
work.

## R5. One script for several goals

The review did not pursue shared mirrored match-arm scripts. The measured
left/right arms shared about 71% of their text after renaming, but differing
constructor-field order, child slots and actual C accesses prevented direct
script reuse. A direction-generic model and C-field abstraction would be
separate design changes. Checked mirroring of the Linux C was rejected.

## History

The [original review](https://github.com/clicklang/click/blob/2175760b9/design/proof-reuse.md)
preserves comparisons, measurements and rejected proposals. Its projected
savings and old `auto`/`execute` snippets are not current instructions.
The [historical solver plan](https://github.com/clicklang/click/blob/2175760b9/design/smt-auto-stage1.md)
is likewise superseded by the current solver and proof/search references.
