# P1: Finish graph-indexed resource lookup

The [rbtree insertion proof](rbtree-example.md) has two unfinished case-3
leaves under a `Right` great-grandparent frame. Its untouched frontier remains
at statement 42. The 2026-09-30 read-identity recheck accepts an inserted
immediate `fold(rb_at(yid), ...)` after unfolding the sibling, including the
recursive child-argument equality that previously failed. The following
`step()` stops on two successors in the inlined rotation. The related
`p->word` / `id->word` store/read regression also passes. No remaining egraph
failure has been established at that next proof boundary.

This issue tracks the shared equality behavior motivated by those proofs and
the bounded resource-lookup cleanup below. Finishing the rbtree proof itself
belongs to [the rbtree issue](rbtree-example.md); a later unrelated proof
failure is not a reason to keep extending this egraph issue. The e-graph and
its resource indexes are part of the **trusted kernel**. The broader design
space is recorded in [Equality closure design](../docs/internals/equality-closure.md),
but that document is not a list of launch requirements.

The pointer interface now exposes one `pointers_known_equal` query backed by
the trusted graph. Mixed whole-offset and cross-block premises compose through
address applications; the old Boolean alias walk is removed. Broader arithmetic
reasoning and guarded memory resolution remain distinct judgments. Insertion
order, late merges, branch isolation, and increasing alias classes have focused
regressions. This cleanup changes no C pointer-value representation.

Int32 known-value equality likewise has one graph query. Its Boolean
fact-component walk and memo are removed; exact-offset no-wrap checks,
load-width guards, and evidence-producing enumeration remain explicit.
Wider scalar theories are future work rather than additional P1 requirements.

## Remaining lookup cleanup roadmap, 2026-10-01

The engineering endpoint is one indexed resource-candidate interface, with no
consumer retrying equivalent pointer spellings or searching an ambient frame
for supporting memory authority. This is a deletion target, not merely a list
of additional graph fast paths. Preserve C pointer representations and the
existing checked distinctions between equality, containment, authority,
provenance, initialization, and snapshot transport.

### Current progress

- Equality queries, completed pointer-read admission, concrete interval
  selection, exact whole-cell payloads, late merges, and persistent fork
  pairing are implemented and tested.
- Producer publication is complete for the audited live resource assembly
  paths: fresh selected inputs capture the graph while empty, checked
  composition/normalization publish whole explicit inputs, and persistent
  descendants maintain pairing through deltas. Retained raw constructors are
  classified as provisional data or structural/empty placeholders in the
  publication audit. This does not make containment selection complete.
- The direct memory `satisfies_fact` migration has passed its red regression,
  control tests, deterministic scaling, and full gate. It shares consumption's
  graph-based address alignment. The remaining retry/normalization paths in
  satisfaction have not been removed; a passing direct query does not complete
  milestone 6.
- General read/write permission still retries spellings and can search all
  resources. Symbolic whole-range readability and storage ownership have
  their own residual lookup paths. Producer publication is complete, but
  containment selection and consumer deletion remain unfinished.

### Seven milestones (milestone 1 complete)

These are seven reviewable outcomes, **not a promise of seven commits**.
Split an outcome into small green slices when necessary, and record completion
here when the old path is deleted. Do not add more resource theories to finish
this list.

1. **Finish resource publication at producers — complete.** The production
   audit and migrations are recorded in the
   [publication audit](../docs/internals/equality-closure.md#resource-producer-publication-audit).
   Fresh trusted assembly now captures the graph while empty; persistent
   deltas preserve pairing, and retained raw lifetimes are explicitly classified.
   The actual framing producer has a red-to-green regression, with sibling,
   snapshot, late-equality, delta, and multi-size work controls. The completed
   scope was: audit production constructors
   reaching memory permission, satisfaction, support, and consumption queries.
   In `src/kernel/functions.rs`, start with single-view satisfaction contexts,
   conditional-control frontiers, returned composite/population body contexts,
   footprint derivation contexts, and access-mode refinement. Separate fresh
   whole-input construction from deltas extending a published context. Publish
   at construction/validation, never on the first lookup. For every retained
   unchecked producer, document why it is structural-only or why publication
   is established before any equality-sensitive query. Tests observe actual
   attachment and cover persistent descendants and unrelated ambient state.
2. **Make candidate identity independent of spelling.** Unify the resource
   candidate contract around retained occurrence IDs and checked address
   alignment. Account for kernel-minted names and retained load origins without
   resolving several spellings in consumers. Review
   `memory_equality_index::indexed_access_entries`: outside exact-cell hits,
   interval selection refuses graph-wide non-affine equalities and any loaded
   pointer. Exact-cell payloads already answer some of these queries. Track
   completeness/unknown at the relevant query/index fragment; do not merely
   remove a soundness guard. An unrelated unsupported term must not force an
   otherwise complete query to search the frame. Include late offset/load
   merges, sibling isolation, width guards, and retained-origin regressions.
3. **Provide bounded symbolic containment support.** Extend the candidate
   contract to existing symbolic range/read/index cases. Graph equality
   identifies addresses and endpoints; arithmetic checks an already selected
   supplier's coverage. Symbolic endpoints are not generally totally ordered,
   so putting every range of an equality class into a bucket and scanning it
   is not a solution. Use indexed exact support where available; when selection
   cannot be bounded, require an explicit checked supplier/footprint witness
   instead of hidden search. Establish how that evidence reaches ordinary
   verification and expansion before changing the callers. Preserve existing
   borrowed-buffer and completed-read regressions. This is the main design
   milestone, and the number of slices it needs is still uncertain.
4. **Delete general read/write permission retries.** Route
   `ResourceContext::permits_memory_read` and `memory_write_range` entirely
   through the shared candidate contract. Remove `pointer_spellings`, the
   per-spelling block searches, and the final `self.iter()` searches. A complete
   indexed miss is final; unknown support is a bounded, actionable refusal or
   an explicitly supplied witness, never another lookup strategy. Keep read
   views distinct from write authority and preserve all permission checks.
5. **Delete symbolic-range read searches.** Migrate
   `memory_state::resource_context_has_symbolic_range_read`. Remove its
   exact-base-then-whole-context retry. Reuse the symbolic supplier evidence
   from milestone 3 and retain element-width, valid-extent, bounds, and
   initialization checks. Test symbolic buffers through equal bases and
   increasing unrelated ranges, including many ranges in the same class.
6. **Unify satisfaction, support, and fragment consumption.** Finish the
   memory paths in `satisfies_fact`, `directly_supporting_fact`,
   `directly_supporting_owned_entry_with_separation`, and
   `without_fact_incrementally`. They still combine graph candidates with
   structural/shape candidates or normalization retries. Return the original
   retained occurrence as support evidence. A multi-fragment requirement may
   visit its explicitly selected suppliers and compute their residuals; it
   must not discover them by scanning a block or normalizing unrelated facts.
   Preserve access mode, separation policy, partial consumption, projection
   dependency, quantities where applicable, and persistent input snapshots.
7. **Finish adjacent storage/object queries and delete obsolete helpers.**
   Migrate `owns_storage_access`, the resource-derived object-provenance lookup
   in `eval/operators.rs`, and callers of `storage_pointer_spellings` in mutex
   initialization and loop storage effects. Object identity is a checked
   storage/provenance judgment, not an arbitrary choice of graph representative.
   Supply that judgment from indexed retained evidence. Remove the spelling
   helper once all callers migrate. Audit the remaining uses of
   `memory_base_facts` and `memory_block_facts`; keep only documented visits
   proportional to explicitly selected input, rather than implicit searches
   for a supplier. Close with source audit, expansion/rechecking, deterministic
   scaling, and the full gate.

Milestones 1–3 establish the common interface. Milestones 4–7 migrate and
remove its remaining consumers; they must not introduce their own alias walks
or containment indexes. Do not implement several independently evolving
fallback replacements in parallel. Milestone 1 is complete. The next
implementation work is milestone 2's shared candidate contract, followed by
symbolic support in milestone 3 before broad caller deletion.

### Meaning of “no scans” and completion

Allowed work includes initial publication proportional to its explicit input,
class/resource delta maintenance, and checking the suppliers selected by an
index or named in a certificate. Ordinary queries must not enumerate equal
spellings, visit an entire pointer block/class to find an owner, or walk the
ambient resource context after an index misses. Moving that search into a
shared helper, query-time attachment, or an eager pairwise cache does not meet
the goal. Smart tactics may perform explicit bounded search, but expanded
simple certificates must carry support so the kernel does not repeat it.

Completion requires all seven outcomes, the named retry/search paths deleted,
and deterministic scaling for hits and misses against unrelated resources,
same-class non-suppliers, equality history, and forks. No existing passing
fixture may silently lose support: reduce any missing case, add indexed or
explicit checked evidence, and keep the full gate green. If a genuinely
incomparable symbolic selection requires new proof-facing support, design that
support explicitly rather than weakening the C or leaving an invisible scan.
The endpoint does not require arbitrary new arithmetic, wider scalar theories,
new term constructors, or finishing every rbtree branch. Further work needs a
concrete new requirement, not another unspecified “next egraph slice.”

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
   owned-cell/instance lookup used by `fold`, and the resource consumers named
   in the cleanup roadmap, must find the same resource
   through addresses the graph proves equal. Index the relevant resources
   so lookup and class updates do not enumerate every spelling or scan
   unrelated state. Replace the spelling retries for these migrated consumers
   once their new paths cover the positive and negative cases. Equality does
   not itself create ownership, prove separation, or transport a value across
   a write; those remain distinct checked judgments.

Work in small green commits. Actual pointer reads, indexed specification reads,
and fold candidate selection have landed. Both the no-write and sibling-write
recursive child matching reductions now pass. The latest rbtree probe is
described under producer-recorded read identities below.
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
indexed miss is decisive. Write-resource selection now uses this same complete
affine interval summary, including interior accesses through late equalities.
Each candidate still requires ownership and the existing write bounds check;
views grant no write authority. Covered hits and misses do not retry spellings
or scan unrelated ranges. Other write shapes retain the general lookup, and
whole-cell read payloads are not treated as complete write candidates.
Exact whole-cell writes now have an ownership-only footprint payload on the
same typed address classes, including late offset and loaded-pointer merges.
The selected live owner supplies its own start for the existing permission
check; views are excluded. Unbound footprints remain unknown and select the
general lookup before candidate checks. Registration remains at proof input
boundaries, and queries do not scan cold frames or unrelated footprint sizes.
Other read shapes still select the general checker
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
frame to attach it. The remaining rbtree proof frontier is tracked separately.

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
Read/fold regressions now pass; resource-lookup deletion remains in the cleanup
roadmap above, and the rbtree proof frontier is tracked separately.

The earlier `codex/egraph-foundation` pointer-representation experiment is
historical reference material, not an integration target. Its failures mixed
an incomplete representation change with semantic gaps. The P1 work does not
require a representation flip.

## Shared read-source admission, 2026-09-30

A consumer-specific snapshot-history rule in `fold` was investigated and
removed. The common typed-read producer now admits source equality for an
exact materialization edge supplying the complete read footprint. A focused
graph regression exercises ordinary equality checking, late address aliases,
and transitivity without resources or `fold`. All consumers query the same
closure. This introduces no extra proof premises, pointer representation
change, or history scan.

The common producer also checks one immediate store transition: structural
object separation or a constant byte gap in an established graph address
class can justify equality between that read and the before-store read. The
full store and read footprints are checked. A focused kernel regression was
red before this rule; ordinary pointer and resource-argument checks now share
its admitted equality. The Click claim in
`mdtests/egraph_pointer_read_single_store.md` already verified through existing
mechanisms and provides expansion/rechecking coverage, not evidence of a new
surface capability. Published single-store edges compose through the graph.

There is no automatic history walk or fold-specific comparison. Unknown
write aliases, unregistered intermediate transitions, and other transition
kinds remain outside this narrow rule. Retained cell-map entries alone are
insufficient: an unknown-alias low-level store can leave them present. Recheck
the actual rbtree leaf before selecting its next missing transition; do not
infer that the complete sibling-write refold now works from this one-edge
regression alone.

## Producer-recorded read identities, 2026-09-30

The sibling-write reduction is now retained as
`mdtests/egraph_recursive_child_sibling_write.md`. It verifies, expands, and
independently rechecks with its C unchanged. Replacing the sibling write with
an overwrite of the pointer field rejects the expanded proof. A resource-free
snapshot-chain regression was red before this change.

Snapshot production now assigns an immutable read-congruence identity.
Recorded cache forgetting inherits the base's identity. A load-valued seeded
run inherits it only if the source and base already share the identity and
slot stride equals value width. This composes sibling materializations copied
from the same unchanged bytes. Graph pointer/int32 load signatures use the key;
existing C values and load terms keep their representation. The metadata is
trusted kernel state and supplies no read permission, lifetime, or framing
judgment. Separate-store evidence remains branch-local. The redundant per-read
cache-forgetting rule is removed.

First interning fixes the key, so late annotation can conservatively miss an
equality but cannot invalidate existing graph signatures. Unknown writes,
havoc, changed sources, constant runs, and unrecorded pruning are negative
regressions. Increasing histories check linear producer work and constant
endpoint-query work without intermediate reads or history traversal.

Rechecking the original rbtree leaf with the immediate refold inserted after
`unfold(xs)` now passes that selected-child comparison. The next existing
`step()` fails because `__rb_rotate_set_parents` has two statement successors.
The untouched frontier remains deliberately incomplete; this is not a claim
that its remaining rotation proof is finished. Original rbtree C and sidecars
are unchanged.

## Sibling-write integration recheck, 2026-09-30

The no-write fixture `mdtests/egraph_recursive_child_alias.md` remains green.
Its sibling-write reduction adds `int tag` to the struct, adds `owns &p->tag`
to the nonempty resource arm, changes the C body to `p->tag = 1;`, and inserts
`step();` between unfold and refold. It still fails with `selected child does
not satisfy the proposed parent model`; the ordinary refold has not been
established by the one-store graph regression.

Bounded investigation identifies the final read's snapshot chain as `Store`
then `CellsForgotten`, then three `CellsSeeded` edges, then the original child
snapshot. The store admission already connects the final read to its immediate
base. A resource-free red regression identified missing equality across a
recorded `CellsForgotten` edge. The shared producer now admits that immediate
no-write edge, with branch isolation, late read aliases, overwrite/havoc
negatives, and constant registration work beside growing older histories.

That one-edge addition does not complete this integration case: constructing
a source load term does not publish a read at each intermediate snapshot.
The next boundary is incremental publication/composition across materialized
and forgotten snapshots. Do not silently add a history walk to equality
queries or `fold`, or claim the rbtree leaf is fixed. Keep this reduction's C
write unchanged and require expansion/rechecking after ordinary verification
succeeds.

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
frontier advances or solve its different-snapshot child matching. At that
checkpoint, both the immediate tree refold above and a version with explicit
field-load equality claims still failed child matching. The subsequent
recursive child-definition slice below closes that no-write reduction.

## Acceptance

- The original `p->word = 5` / `id->word == 5` case and a reduced rbtree
  read/fold case verify through the new paths, with unchanged C. The separate
  rbtree issue owns the two unfinished case-3 leaves and their frontier pin;
  a remaining unrelated proof gap does not expand this issue's scope.
- A regression shows a pointer read registered **before** a later proved
  address equality and checks the resulting loaded-value equality. Cover
  insertion order, branch isolation, withdrawal or restriction of evidence,
  snapshot and type separation, volatile reads, and an unavailable read or
  missing owner. Both ordinary verification and expansion/rechecking agree.
- All seven cleanup outcomes above are met, including deletion of the named
  spelling retries and ambient/block supplier searches. Published descendants
  and explicitly supported symbolic queries respect the scaling contract.
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

- Migrate pointer consumers beyond the named resource/storage cleanup, such
  as broader loan, retirement, validity, framing, effect, and diagnostic
  judgments. Retire their legacy alias walks when each one has a complete
  replacement. General read/write permission and the named storage queries
  are now in the bounded cleanup roadmap above, not deferred future work.
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

## Recursive child-definition slice

`mdtests/egraph_recursive_child_alias.md` now unfolds at `p` and refolds at
an equal model identity, with no C writes or intermediate load-equality
claims. The red test previously proved explicit field-load equalities but
failed at the child argument comparison. Checked child-expression evaluation
was discarding its typed read definition; its cached scalar-cell conversion
also omitted the pointer producer metadata carried by the symbolic route.

After all existing readability and argument prerequisites pass, the kernel
retains certified typed read definitions in the graph's shared term metadata.
This adds no proposition premise, address hypothesis, read authority, or
snapshot transport. Both unfold and fold retain their child-index definitions,
and equality comparison uses the existing graph query. Expansion independently
rechecks the same resource consumer. Kernel controls reject fabricated and
volatile producer evidence and keep different snapshots distinct.

This completes the no-write generic child matching reduction above. The
rbtree probe's differing recorded snapshots remain a separate question; this
slice does not claim to advance its frontier.
