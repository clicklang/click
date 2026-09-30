# P1: Use kernel equality for rbtree pointer reads and folds

The [rbtree insertion proof](rbtree-example.md) has two unfinished case-3
leaves under a `Right` great-grandparent frame. The 2026-09-29 recheck on
`f01a85a1a` confirms the frontier is unchanged. An attempted immediate
`fold(rb_at(yid), ...)` after unfolding the sibling now passes owned-cell
consumption, then fails the recursive child-argument equality check. This is
no longer established as an owned-cell lookup failure. The related
`p->word` / `id->word` store/read regression already passes.

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

Work in small green commits. Actual pointer reads, indexed specification reads,
and fold candidate selection have landed; next isolate the child-argument
equality boundary described below.
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
execution. A completed nonvolatile typed read registers its exact defining
equation with the path context, which files an equality between that existing
C value and `load(snapshot, address)` in the graph. Pointer equality queries
use the resulting closure, including address equality learned after the read.
This adds no theorem premise or read permission. An owned range's
read/write membership check now uses graph equality when comparing an access
to that range's selected base; the held range still supplies authority and its
bounds still decide coverage. Fold consumption now uses a persistent paired
resource/class address and concrete-span index, including late merges and
displaced aliases, without enumerating pointer spellings. Specification-read
candidate selection uses a persistent interval summary for concrete affine
addresses in classes with positive concrete read cores, including mixed extents
and overlapping views. It delivers only covering candidates lazily, and an
indexed miss is decisive. Other read shapes still select the general checker
before lookup. Whole-cell reads now attach their exact-start entries to typed graph address
applications. The graph's term-merge stream propagates offset and loaded-pointer
equalities to these entries, including late equalities after resource
publication. Fold selection consults the same payload. Whole-cell hits use this payload
with input registration and per-occurrence authorized-footprint eligibility.
Different-sized or symbolic ranges elsewhere in the class do not disable a
known cell match. Unbound classes remain unknown rather than denying arithmetic
or snapshot-based reads; broader symbolic containment, partial-range reads with offset aliases,
and snapshot matching still use the general checker. Initial registration
belongs to the execution proof input boundary; lookups cannot scan a cold
frame to attach it. The rbtree acceptance remains open.

The previous attempt to publish `load(M, p) == value` as a certified
`ExecutionPureFact` was reverted: it changed execution theorem shapes by
adding an implication premise and broke recursive resource child-argument
checking. The graph equality worked, but the fact channel was the wrong
carrier. The current bridge retains genuine load-site evidence in the trusted
path context without changing logical premises. The
[late-address-equality fixture](../mdtests/pointer_loads_equal_after_late_address_equality.md)
reads two pointer fields before a three-link address equality and closes their
value equality with one `simp()`. Kernel regressions check insertion order,
branch isolation, withdrawal, snapshot separation, and volatile exclusion.
The rbtree read/fold and resource-lookup acceptance work remains open.

The earlier `codex/egraph-foundation` pointer-representation experiment is
historical reference material, not an integration target. Its failures mixed
an incomplete representation change with semantic gaps. The P1 work does not
require a representation flip.

## Reduced rbtree recheck, 2026-09-29

The untouched frontier still reports statement 42, `augment_rotate(gparent,
parent)`, with nine completed breaks and four continues. Inserting an immediate
refold after the first `unfold(xs)` in a `RbTree::Node(yid, yp, ycol, yl, yr)`
arm fails with `selected child does not satisfy the proposed parent model`.
Temporary bounded diagnostics identify the left child's sole C pointer
argument as unequal; its model field, resource name, and schema match.
Owned-cell consumption has already succeeded before this check.

At the recheck checkpoint, the following independent reduction failed at the same child check. Changing
only `fold(tree(id), ...)` to `fold(tree(p), ...)` verifies. An explicit
`have p == id by { simp(); }` verifies, but an additional
`have p->left == id->left by { simp(); }` fails. There are no C writes.
This points to resource child-load equality, rather than parent-cell candidate
selection. Temporary diagnostics show the reduction's two child values carry the same
registered load variable and defining snapshot; querying its explicit load
application succeeds, while comparing the existing pointer values in the
graph fails. This suggests a missing checked value-to-load connection in
resource evaluation, rather than a congruence failure. It is not permission
to infer a read site from a storage-relative pointer value.

The actual rbtree probe differs: the recorded child load origins have equal
source addresses but different snapshots. A same-snapshot bridge fix alone
is therefore not established as sufficient. After fixing and checking the
small resource-evaluation case, recheck the real leaf and justify any needed
snapshot transport separately. Do not equate different snapshots merely
because their load addresses are equal.

```c
struct node { struct node *left; struct node *right; };
void roundtrip(struct node *p) {}
```

Save that C as `egraph_reduce.c` beside this sidecar:

```click
verifying "egraph_reduce.c";
spec enum Tree { Empty, Node(struct node*, Tree, Tree) }
resource tree(p: struct node*) {
 field model: Tree;
 match model {
  Tree::Empty => { fact p == 0; },
  Tree::Node(id, lm, rm) => {
   owns &p->left;
   owns &p->right;
   owns left: tree(p->left);
   owns right: tree(p->right);
   fact p != 0;
   fact p == id;
   fact left.model == lm;
   fact right.model == rm;
  },
 }
}
void roundtrip(struct node* p) {
 owns t: tree(p);
 requires t.model != Tree::Empty;
 ensures t.model == old(t.model);
} by {
 match t.model {
  Tree::Empty => { contradiction(t.model == Tree::Empty); },
  Tree::Node(id, lm, rm) => {
   let { left: l, right: r } = unfold(t);
   let t = fold(tree(id), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
   execute();
   simp();
  },
 }
}
```

The reduction is diagnostic evidence, not evidence that rbtree verifies.
The original C remains unchanged. Expand and recheck the successful control;
do not expand the failing frontier or failing reduction.

## Specification-read slice after the recheck

The [small nonrecursive regression](../mdtests/egraph_resource_pointer_load_alias.md)
now verifies `p->next == id->next` after unfolding one pointer-cell resource.
Both `p == id` and field-address equality already verified before this fix.
The typed specification-load producer now retains its exact value-to-load
mapping as trusted graph term metadata, independent of proposition premises.
Context reconstruction retains those definitions; each proof context still
needs its own address evidence. `simp` emits the existing graph-aware
`normalize() using {}` checker without searching for premises.

Controls cover ordinary contract equality and same-spelling reads. Kernel
regressions cover branch-local address evidence, changed snapshots, missing
read authority, pointer arithmetic, reconstruction, stale equality misses,
and deterministic lookup scaling beside 16, 64, 256, and 1024 unrelated
logical load definitions. This slice does not establish that the rbtree
frontier advances or solve its different-snapshot child matching. Rechecking
both the immediate tree refold above and a version with explicit field-load
equality claims still fails child matching; the specification claims now pass.
Keep that resource-child boundary separate from this completed read slice.

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
