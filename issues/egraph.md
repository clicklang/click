# P1: Use kernel equality for rbtree pointer reads and folds

The [rbtree insertion proof](rbtree-example.md) has two remaining case-3
leaves under a `Right` great-grandparent frame. An unfold publishes owned
cells using a loaded pointer's spelling, but a later `fold(rb_at(yid), ...)`
cannot consume them through a proved-equal binding. The related regression
stores through `p->word` and then asks for `id->word` after proving `p == id`.
Today, local spelling retries handle parts of these cases, but load equality
still blocks the rbtree leaves.

This P1 issue is limited to the equality behavior needed to finish those
proofs. The e-graph is part of the **trusted kernel**. The broader design
space is recorded in [Equality closure design](../docs/internals/equality-closure.md),
but that document is not a list of launch requirements.

## Required behavior

1. **Reliable address equality.** Given checked equalities such as `a == b`
   and `b == c`, the graph answers equality for `a`, `c`, and their equivalent
   displaced addresses. A late equality must update previously registered
   applications. Queries must not lose an equality when another fact is added,
   depend on insertion order, or stop at an arbitrary congruence depth.
   Branches and restricted proof contexts keep their own evidence. Much of
   this foundation has already landed; complete only gaps exposed by the
   rbtree regressions.
2. **Checked equality for actual pointer reads.** A completed, nonvolatile
   pointer read supplies checked, path-local evidence relating its existing C
   value to a graph term `load(snapshot, address)`. Equal source addresses
   at the same snapshot then give equal loaded values, including when the
   address equality is learned later. Preserve the current C pointer-value
   representation. Do not infer a load site by decoding a storage-relative
   pointer, add the bridge as an ordinary proposition premise, grant read
   permission with equality, or identify loads from different snapshots
   without separate checked evidence.
3. **Equality-aware reads and fold consumption.** Specification reads and the
   owned-cell/instance lookup used by `fold` must find the same resource
   through addresses the graph proves equal. Index the relevant resources
   so lookup and class updates do not enumerate every spelling or scan
   unrelated state. Replace the spelling retries for these migrated consumers
   once their new paths cover the positive and negative cases. Equality does
   not itself create ownership, prove separation, or transport a value across
   a write; those remain distinct checked judgments.

Work in small green commits: connect a real pointer read to the graph, use it
in one live comparison, then migrate specification reads and fold consumption.
If the rbtree failure turns out to be a resource-lookup gap with the needed
load equality already available, take the lookup slice first. Do not change
the unchanged C to route around a verifier gap.

## Current implementation and known boundary

`kernel::equality_graph::EqualityGraph` already exposes `add_equality` and
`are_equal` inside the trusted kernel. Its persistent, path-local fragments
cover affine pointer classes, whole offsets, int32 addition and scaling, and
registered same-snapshot pointer and four-byte scalar loads. Selected
normalization and int32 consumers query it. The graph's pointer-load term is
distinct from the storage-relative pointer value produced by ordinary C
execution. Resource lookup still has compatibility spelling retries.

The previous attempt to publish `load(M, p) == value` as a certified
`ExecutionPureFact` was reverted: it changed execution theorem shapes by
adding an implication premise and broke recursive resource child-argument
checking. The graph equality worked, but the fact channel was the wrong
carrier. The next bridge must retain genuine load-site evidence in the
trusted path context without changing logical premises. Direct comparisons
of loads through addresses already known equal passed before this attempted
change, so they are not evidence that the new bridge works.

The earlier `codex/egraph-foundation` pointer-representation experiment is
historical reference material, not an integration target. Its failures mixed
an incomplete representation change with semantic gaps. The P1 work does not
require a representation flip.

## Acceptance

- The original `p->word = 5` / `id->word == 5` case and a reduced rbtree
  read/fold case verify through the new paths. The two blocked case-3 rbtree
  leaves then verify with the unchanged C, and `tests/examples.rs` pins the
  advanced frontier. A passing synthetic example alone is insufficient.
- A regression shows a pointer read registered **before** a later proved
  address equality and checks the resulting loaded-value equality. Cover
  insertion order, branch isolation, withdrawal or restriction of evidence,
  snapshot and type separation, volatile reads, and an unavailable read or
  missing owner. Both ordinary verification and expansion/rechecking agree.
- Migrated specification reads and fold consumption use equality-aware
  indexed lookup, including resources inserted before and after a class
  merge and displaced aliases. Their superseded spelling retries are removed.
  No equality query performs frame search or grants permission.
- Deterministic multi-size regressions cover equality chains, late
  same-snapshot load merges, resource lookups through growing alias classes,
  and branch forks. The work respects the
  [verification-efficiency contract](../docs/internals/verification-efficiency.md).
  The relevant focused checks and the full `scripts/check.sh` gate pass.

## Possible future direction, outside this P1 issue

Broader use of the same kernel equality service is desirable, but it is not
required to finish the rbtree leaves. Consider each extension only when a
concrete proof needs it, with its own soundness and scaling review:

- Migrate other pointer consumers, such as general read/write permission,
  loans, retirement, validity, framing, effect lookup, and diagnostics. Retire
  their legacy alias walks when each one has a complete replacement.
- Add other sorted term constructors, scalar widths, algebraic constructors,
  pure functions, and more tactic matching modulo equality. Existing int32
  work does not imply those theories are already supported.
- Add explicit checked transport of load equality across snapshots where a
  proof needs it. Equality comparison itself should not search for frames.
- Consider an `explain` interface if a concrete user-facing or kernel
  consumer needs it. Expansion can recheck the trusted graph query without
  printing an internal derivation.

The [design note](../docs/internals/equality-closure.md) and earlier Git
history retain the detailed implementation ledger and investigated options.
They are reference material, not additional P1 acceptance criteria. A newly
discovered soundness bug is still urgent under the general
[P1 policy](README.md), irrespective of this issue's narrower scope.
