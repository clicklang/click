# Decide equality with one e-graph in the kernel

Plan revised 2026-09-27 after takeover review. This replaces the previous
fixture-by-fixture loaded-pointer flip plan. The implementation is partial;
the milestones below describe work still to do.

P1. The kernel records facts, owned cells, and load names under whichever
spelling of a term produced them. Each lookup site then decides for itself how
much of a proved equality to consult. This keeps reappearing as proof failures
on true claims, and each local repair covers only one hop at one site. It also
blocks the Linux rbtree insert proof: see
[rbtree-example.md](rbtree-example.md), state of 2026-09-26.

The design is in
[Equality closure design](../docs/internals/equality-closure.md). This
issue tracks building it.

## Violated invariant

Once a proof has established `a == b`, every kernel judgment about a term that
contains `a` must give the same answer for the same term with `b` in its place:

- fact availability;
- read and write permission;
- consuming owned cells or instances on a fold;
- the value of a load;
- decisions on C conditions.

The kernel must do this without the author restating the fact under the other
spelling, and at a cost that respects the complexity contract in
[Verification efficiency](../docs/internals/verification-efficiency.md).

The original inventory found the invariant split across these structures;
the partial pointer classes now sit alongside them:

- one-hop pointer alias indexes;
- three different pointer-equality walks, one of which rescans every
  condition fact at each step;
- a 32-bit equality graph, rebuilt after every insertion once queried;
- `ConstantClasses`;
- a separate 64-bit adjacency map;
- exact-only algebraic equality.

Load variables are keyed by exact pointer spelling. The explicit tactics
(`assumption`, `apply ... using`, `normalize() using`, `rewrite`) match
premises exactly, up to orientation.

## Evidence

Four failures of this one class in the rbtree campaign:

- **Gap 72** (fixed locally in a3b96c12): read permission through an alias.
  `pointer_spellings` now tries up to three spellings.
- **Gap 74** (fixed locally in 4d5d6f6d): a fold's body fact lowered a frame
  identity through its proved-equal C local. Fixed by substituting one pointer
  variable with one exact alias and retrying.
- **Original fold-consumption failure, partly repaired.** The fold
  `fold(rb_at(yid), ...)` could not consume cells an
  unfold published under the loaded pointer's spelling ("fold requires
  ownership of the complete instance body"). `without_fact_incrementally`
  originally never consulted aliases. Class-based spelling retries now find
  the cells, but load equality still stops the `Right` great-grandparent
  leaves of the insert fixup's case-3 rotation, and the frontier in
  `examples/rbtree-insert/rbtree_insert.frontier` stands there.
- **Load after a store, locally repaired.** After `p->word = 5` with
  `p == id` proved,
  `have p->word == 5` held but `have id->word == 5` was refused. A spelling
  retry now handles this fixture; it is not yet an indexed closure lookup.

## Intended regressions

1. **Load through an alias after a store.** An mdtest where a frame resource
   names its cell by a model payload `id`, the C code stores through a pointer
   `p` loaded from memory, and the proof has `p == id`. Both spellings must
   then read the stored value:

   ```c
   struct node { unsigned long word; struct node *up; };
   void set_up_word(struct node *c) { struct node *p; p = c->up; p->word = 5; }
   ```

   ```click
   spec enum Frame { Up(struct node*, int) }
   resource frame_at(c: struct node*) {
       field model: Frame;
       match model {
           Frame::Up(id, value) => {
               owns &c->up;
               owns id->word;
               fact id != 0;
               fact c->up == id;
               fact id->word == value;
           },
       }
   }
   // proof: match f.model; unfold(f); step(); step(); step();
   //   have p == id by { simp(); }
   //   have p->word == 5 by { simp(); }
   //   have id->word == 5 by { simp(); }   -- retain the landed regression
   ```

2. **Fold at an arm binding over cells published under another spelling.** The
   same shape as the rbtree leaf: unfold a child reached through a load, then
   `fold` it at the proof arm's binding for that pointer. It must consume the
   cells.
3. **Two-hop and displaced aliases.** Given `a == b` and `b == c`, facts, cells,
   and loads at `a + 8` must be found through `c + 8`. The same must hold
   through an offset spelled two ways (`p + 8` and `(p + 4) + 4`).
4. **Explicit tactics modulo the closure.** `normalize() using { a == b; b == c; }`
   closes `a == c`. Today it cannot; see
   `examples/rbtree-model/README.md`, parent consistency.
5. **Scaling.** Deterministic curves over several input sizes for:
   - a chain of `N` pointer equalities;
   - `N` loads through aliases;
   - a proof with many branches that each add equalities.

   Work must be near-linear in the facts and terms a path adds. It must stay
   flat in unrelated ambient facts. Per-branch persistence must not clone the
   graph.
6. **Soundness negatives.**
   - Two terms that were never proved equal do not meet.
   - A merge of two different constructors, or of two distinct constants of
     the same sort, reports contradiction.
   - Loads at different memory snapshots do not meet by congruence.

## Direction

Keep the goal: one kernel equality service, with congruence closure and no
saturation. Equalities enter from hypotheses, checked proof steps, and
execution. The service propagates their consequences through registered
applications; it does not search for arithmetic identities or rewrite rules.

The next milestone is a coherent pointer-and-load foundation, not a smaller
failure count on the old trial. Keep the useful affine pointer classes and
constructor centralization where they fit, but replace the recursive load
normalizer and spelling retries rather than extending them.

The detailed invariants and API boundaries are in
[Equality closure design](../docs/internals/equality-closure.md). In particular:

- Term identities and global load naming are assumption-free. Equalities,
  congruence indexes, resource indexes affected by equality, and provenance
  evidence belong to the path's persistent context.
- A loaded pointer denotes the stored pointer value, independently of the
  address spelling and pointee width used to read it. Construction, decoding,
  displacement, rewriting, and diagnostics must agree on that representation.
- Loads include their snapshot and access interpretation. Same-snapshot
  congruence is automatic; different snapshots require checked frame evidence.
- Equality comparison performs no frame search. Execution may retain a name
  when its existing checked preservation rule permits it; explicit transport
  can establish additional cross-snapshot equalities and feed them to closure.
- Every query observes completed congruence closure over the registered terms.
  No semantic depth cap, insertion-order dependence, or loss of an equality
  when another fact is added is acceptable.
- Index resources by equality-aware address keys. Enumerating all alternative
  spellings on each lookup is not the destination.
- Keep C unchanged. Every stage lands green, with the old mechanism deleted
  for the consumer that has migrated.

## Implementation progress (2026-09-27)

The next integration slice exposes the existing implementation as
`kernel::equality_graph::EqualityGraph`, with `add_equality` and `are_equal`.
It remains trusted kernel code with pointer-typed operands and no `explain`
requirement. Pointer spelling helpers remain explicitly separate. This is a
behavior-preserving interface refactor; additional equality sorts and consumer
migrations follow one green commit at a time. The broad unmerged
`codex/egraph-foundation` draft is reference material, not the next merge target.

The first additional consumer is `normalize() using`: after validating its
cited premises, it uses the current trusted equality graph during reduction to
decide pointer-equality leaves and conditional-expression guards. Failed
queries stay unknown, and conditional reduction does not enter binder bodies. Ambient equality is deliberately available;
other uncited conditions are not. This preserves the current term representation
and adds no frame search or proof explanation. The graph now also retains
explicit whole pointer-offset equalities, so normalization can prove transitive
equalities between ordinary C pointer parameters without migrating their
representation. The offset fragment also maintains addition congruence using
indexed parent uses and weighted class merges, including when operand
equalities arrive after the addition terms. It adds no arithmetic solver or
cancellation rule, and no ownership or framing consumers have been migrated
to it.

The graph now also admits explicit int32 equalities. Normalization uses their
transitive closure for equality leaves and conditional guards through the same
query traversal. Typed scalar nodes share the offset fragment's persistent
term-class engine; no separate scalar union-find was added. Regressions cover
branch isolation, sort and snapshot separation, withdrawal and restriction,
expansion/rechecking, and multi-size indexed insertion/fork work. Canonical
edge support counts avoid raw-load interning across verification arenas; a
multi-size regression rejects the whole-snapshot comparisons that exposed. Further scalar operators remain future chunks.

Int32 equality now propagates into same-width scaled offsets through the shared
application-signature and parent-use indexes, including late merges and nested
offset additions. Literal indices also join their folded byte constants with
checked multiplication. Thus normalization can prove `p + i == p + j` from
`i == j` for the same pointer base. Widths, 64-bit signedness, and memory
snapshots remain distinct; no cancellation, scalar arithmetic, ownership, or
framing rules were added. Regressions cover expansion/rechecking, withdrawal,
restriction, persistent forks, and deterministic multi-size affected-parent
and fork work.

Int32 addition now participates in the same application worklist. Operand
merges propagate through nested sums and scaled pointer offsets; literal sums
join their wrapping bitvector values without discharging C signed definedness.
Registration canonicalizes the input once and interns shallow child IDs.
Regressions cover late merges, constant folding, snapshot and branch isolation,
withdrawal/restriction, expansion/rechecking, and multi-size registration,
propagation, and fork work. Other scalar operators, arithmetic solving,
cancellation, ownership, and framing remain outside this slice.

Registered int32 loads now have same-snapshot congruence within one exact
storage block. The shared application signature includes the defining snapshot
identity and offset class; indexed parent uses propagate late equalities.
Nested load-index registration is iterative. The graph reads the registered
definition, not the mutable live origin, and does not change global load names.
The surface regression proves equal array reads from equal indices and expands
and rechecks. Negative coverage keeps relevant stores, storage blocks, access
widths, omitted premises, branch assumptions, and read permissions separate.
Multi-size regressions cover registration, late closure, and persistent forks.
Cross-snapshot framing, block-equality integration, and resource lookup remain
separate work.

An end-to-end transport composition checkpoint now verifies a store to `p[k]`,
a checked frame equality for `p[i]` from `i != k`, and graph normalization of
`p[j]` from `i == j`. The existing interfaces already compose; this checkpoint
adds regressions and documentation rather than a new kernel mechanism.
Expansion rechecks, omitted bridges and missing premises fail, overlapping
stores are rejected, and a supplied equality for one read neither merges whole
snapshots nor leaks into sibling contexts. Removing that edge preserves the
same-snapshot equalities and withdraws its cross-snapshot consequences.

True offset premises now also populate scalar graph edges when both sides
have the existing checked four-byte element-index interpretation. This shares
support counting with explicit scalar premises and preserves withdrawal,
restriction, and persistent fork isolation. Multi-size regressions cover
insertion and congruent queries.

A global replacement of the legacy Boolean scalar query is deferred: its
exact-pointer-offset callers cannot accept every wrapping int32 equality the
graph proves. The existing wrapped-index regression caught this boundary;
the broader replacement was discarded. A future consumer migration must make
the exact-offset versus residue-equality contract explicit first.

Memory resolution now applies the existing exact-index rebuild check when it
uses a scalar equality to affirm an offset equality. This closes a preexisting
hole for explicitly asserted wrapping scalar equalities, independent of graph
integration. The same tests show that nonwrapping equalities still work at
element widths 1, 4, and 8. The broader scalar-query migration remains future
work because its other consumers still need review.

The shallow Boolean int32 equality decision now uses the shared graph. This
brings addition and registered same-snapshot load congruence into that one
consumer while retaining the exact-offset guard at its memory-resolution
caller. Branch, snapshot, wrapping-offset, and multi-size regressions cover
the migration; the broader legacy fact-path helper remains in use elsewhere.

The full int32 equality condition decision now also queries a graph with
established term equivalences before memory resolution and its other arithmetic
rules. An empty graph skips interning unrelated terms. Regressions cover
addition, same-snapshot loads, branch scope, wrapped offset refusal, resource
quantity work, and multi-size decisions without building the legacy fact
index. Transport, memory, and resource consumers of that index remain future
slices.

Int32 fact transport now checks the graph before its legacy fact-path lookup
when the graph has established equivalences. Order-fact matching can use
congruent sums and registered same-snapshot loads without building that index.
The old lookup and structural transport remain for term forms outside the
graph; memory and resource consumers have not moved. Branch withdrawal,
snapshot separation, and multi-size query work have direct regressions.

The int32-addition matcher now asks the same graph for equality of individual
addends. This composes a reordered sum with registered same-snapshot load
congruence. A direct graph match avoids the legacy fact index; a nonmatching
candidate in the existing greedy matcher may still build it first. Tests cover
changed snapshots, withdrawn premises, and multi-size reassociated matching;
the graph itself still does not reorder addition.

Direct memory-resource matching now asks the graph for equality of its int32
range start and end values. The resource base still uses its pointer check;
this does not turn wrapping index equality into exact byte-offset equality.
Regressions cover same-snapshot load endpoints, a changed snapshot, premise
withdrawal, and multi-size matching without building the legacy fact index.

Checked `CValue::Int32` comparison now queries the graph before broader memory
resolution. Composite/token and instance resource matching use this shared
typed value rule for arguments and fields, removing the resource-specific graph
check. Direct C-value regressions cover same-snapshot loads, withdrawal,
overwrite, and multi-size queries without the legacy fact index. Byte-typed
and pointer values keep their existing rules.

Contract certification of true `Bitvector32Equal` claims now uses the typed
int32 value rule after checked cross-snapshot load framing. Direct regressions
cover same-snapshot graph congruence, overwrite and withdrawal boundaries, and
multi-size certification without the legacy fact index. Pointer-offset
certification remains separate.

Selected range-composition candidates now rely on the graph-backed int32
condition decision for endpoint equality, without a redundant second legacy
fact-path walk. A direct join regression checks graph-congruent endpoints and
withdrawal. Candidate indexing remains narrower: normalization does not yet
select every pair whose endpoints are related only by graph congruence.

Resolved four-byte scalar loads now compare their established values through
the int32 graph before the legacy fact-path lookup. Memory resolution remains
the authority for the load's value and snapshot; this adds no read or frame
permission. Other widths keep the existing path. Regressions cover both
directions, overwritten and withdrawn evidence, a one-byte load, and multi-size
queries without building the legacy fact index.

Two resolved four-byte loads now compare their checked stored values through
the int32 graph before the legacy fact index. This handles distinct load names
whose values are graph-congruent, without merging their snapshots or widening
the rule to other widths. Regressions cover withdrawal, overwrite, a resolved
one-byte load, and multi-size query work.

The first implementation chunk replaces the bounded load normalizer in
the pointer fragment (now `kernel/equality_graph.rs`) with maintained same-snapshot application signatures and
an iterative merge worklist. This fragment recognizes already-opaque,
registered pointer-width load blocks. It does **not** yet change all C loads
to that representation, migrate resource indexes, or complete milestone B.

- Reproduced the lost-equality bug: two loads compare equal, then cease to
  compare equal after each enters an explicit class. The replacement merges
  those classes, including late address merges and all six equality orders.
- Load-address uses are indexed by block. Merging classes reindexes only users
  of moved blocks; class weight includes those uses to avoid moving a large
  shared prefix into a fresh alias on every branch.
- Signatures contain snapshot arena IDs, address representatives, and compact
  affine-offset IDs. Machine atoms retain interned terms; hot signature keys
  do not compare memory snapshots or nested load trees. Legacy spelling
  reconstruction retains structural ordering, independent of atom ID order.
- Query registration and closure are iterative and branch-local. Clones share
  persistent roots, not mutable closure state. Restrictions and withdrawals
  rebuild from remaining premises and discard their removed consequences.
- Removed `proves_equal_in` and its comparison-time frame search. A separate
  checked frame derivation can supply an equality; comparison alone does not
  transport loads between snapshots.
- Regressions cover twelve nested loads, displaced aliases, width eligibility,
  snapshot separation, restricted premises, and branch isolation. Scaling
  tests use sizes 16/64/256/1024 for same-snapshot ambient loads, late merges,
  repeated queries, branch extensions, and explicit affine input; balanced
  merge tests extend to 4096 blocks. These do not yet establish a bound for
  every growing symbolic affine-delta pattern or resource-index migration.

The rewrite audit traced certificate checking through `ProofStep::Rewrite`,
`finish_rewrite`, and the generic focused-result publisher. Equality substitution
now lives in `kernel/proof/equality_rewrite.rs`. `ProofFacts::check_equality_rewrite`
checks the cited equality (or its reverse) against the persistent exact premise
index and constructs a private `CheckedEqualityRewrite`. Only the kernel can
change its semantic result or turn it into a proposition obligation. A proposed
surface spelling must pass the existing checked, corresponding-leaf load
transport before replacing that result. Smart planning can still construct
candidates over an explicit premise slice; those candidates have no proof
authority and the certificate path does not use their premise search.

The binder guard refuses substitution under `forall`/`exists` when it would
shadow an equality variable or capture its replacement. Its bounded collector
sees pure-function arguments and treats snapshots as opaque. Direct kernel
regressions cover missing and reversed premises, sibling-context isolation,
forged presentation rejection, capture, and flat work as unrelated premises
and snapshot contents grow. The source-level probe did not demonstrate an
exploit. Goal lowering/unfolding and the generic publisher remain their existing
trust boundaries; this change gives equality substitution its own checked rule,
not a migration of every proof transition.

Next: settle same-block offset/atom updates and make the constructor/decoder
representation change coherent through mandatory consumers. Before that switch,
resolve the current load registry's sharing of names across access widths;
pointer-load interpretation must be part of its identity. The design selects a
distinct pointer-load name and explicit loaded-pointer block variant so scalar
walkers cannot silently treat it as a bitvector variable. Then integrate
indexed read/fold lookup and complete the full milestone-B regressions before
a broad consumer handoff.

## Why the migration changes

The takeover review found these concrete obstacles in the previous partial
work. Items 1, 2 (the load scan), and 4 are addressed by the fragment above;
the representation mismatch and resource/earlier-load scans remain migration
work:

1. `PointerClasses::normal` stops after `LOAD_CONGRUENCE_DEPTH = 4` and returns
   immediately for a pointer already in an explicit class. It does not merge
   two explicit classes when their loaded members become congruent. Pin the
   case `p == q`, `load(M,p) == x`, `load(M,q) == y`, concluding `x == y`,
   including all insertion orders and adding facts after an earlier query.
   This was reproduced and is now covered by an executable regression.
2. Load normalization scans classed loads in the queried snapshot. The current
   scaling regression adds loads in other snapshots, so it does not cover
   the expensive case. Alias enumeration in resource consumption and the
   trial's earlier-load scan have similar repeated-work risks.
3. The trial changes `Pointer::loaded` while leaving `Pointer::as_loaded`
   decoding the old representation. Its remaining failures mix an incomplete
   interface change with actual semantic gaps. Fix the interface together
   before using those failures to justify new reasoning rules.
4. `PointerClasses::proves_equal_in` invokes frame reasoning during comparison,
   contrary to the verification-efficiency contract. Restore the boundary
   between deriving an equality and querying the closure of known equalities.

## Milestones

### A. Settle the pointer/load contract and executable regressions

This is the first implementation chunk. Work in an isolated branch/worktree.

- Reproduce the explicit-class congruence failure above. Add nested-load,
  late-merge, insertion-order, and branch-isolation cases at the kernel API.
  Intermediate commits must remain green; do not commit knowingly failing
  tests as a checkpoint.
- Define the semantic constructor/decoder API for a loaded pointer. The
  decoder should expose the load identity/origin and pointer displacement,
  rather than require a storage-relative block and scaled integer payload.
  Specify how typed access and pointer casts preserve value identity.
- Specify stable term IDs, the weighted pointer relation, application
  signatures and parent-use indexes, merge propagation, resource reindexing,
  and equality evidence. Resolve same-block offset equations and equal offset
  atoms explicitly; the existing block union-find alone does not handle them.
- Resolve the `rewrite` trust question now: trace its certificate path and
  identify the kernel check for equality substitution, or add the required
  checked rule. Do not infer a soundness bug merely from its absence in the
  original inventory. The foundation must have a demonstrated evidence path
  before other consumers depend on it.

Exit: a concrete API/design and regressions establishing what the foundation
must guarantee, with no unresolved representation or trust-boundary choice
hidden in a consumer migration.

### B. Build and integrate the pointer/load foundation

This is the main hard part. It can take several green commits, but the
representation change must be coherent when integrated.

- Maintain incremental congruence using indexed application signatures and
  affected-parent worklists. Updating an address class must merge existing
  congruent loads, including loads already equated to other values. Complete
  pending work before answering a query; batching must not expose stale state.
- Use stable IDs and persistent indexes. Account for affine payload size,
  branch forks, merge maintenance, and explanation size, not just the number
  of union operations. Reconsider the representation if these costs violate
  the complexity contract.
- Change constructor and decoder together and migrate their mandatory
  consumers. Preserve assumption-free names; do not adopt the trial's scan
  of every earlier load to choose a name.
- Keep checked frame derivation outside comparison. Add derived equalities
  only to the context justified by that derivation and its premises.
- Integrate indexed resource lookup through at least specification reads and
  fold consumption. Handle resources registered both before and after class
  merges, displaced aliases, and representatives that change later. Remove
  those consumers' spelling retries.
- Review lost separation by cause: missing lookup, missing frame evidence,
  incomplete decoding, or missing provenance. Derive provenance from supported
  C semantics and checked lifetime/reachability facts; never infer it from a
  borrowed storage block. Snapshot identities form a DAG, so do not implement
  the old plan's "earliest birth snapshot" as a numerical minimum or assume
  unrelated branch snapshots are ordered. Allocation claims are not proof of
  an allocation's birth in a snapshot.
- Verify the original alias-store and rbtree fold/load shapes, including their
  negative cases. Finish ordinary verification before expanding tactics.

Scaling axes, at multiple sizes: equality chains and balanced merges; nested
loads; many unrelated loads in one snapshot; repeated loads across stores;
resource lookups through large alias classes; resources present before many
merges; branches extending a large shared prefix; and restricted contexts.
Measure total work as well as individual query work. A fixed corpus timing
and a test varying only other snapshots are insufficient.

Exit: constructor/decoder agreement, complete pointer/load congruence for the
specified fragment, checked evidence, indexed read/fold consumers, deterministic
scaling regressions, and the full `scripts/check.sh` passing. The old trial's
failure count is not an acceptance criterion.

### C. Migrate remaining pointer consumers and delete the old mechanisms

After milestone B, migrate one bounded subsystem at a time: read/write
permission, loans, heap retirement, validity, remaining resource matching,
then effect/transport lookup and diagnostics. Each change names its old code,
uses the established API, adds positive/negative and ambient-scaling coverage,
and deletes the superseded mechanism for that consumer.

Complete removal of `exact_pointer_aliases`, the pointer equality walks,
`pointer_spellings`, `resolve_symbolic_pointer_alias`, and minted-load scans
once their final consumers move. Do not call stage C complete while a fallback
still silently supplies a different equality relation. Resource containment
and ordering remain separate judgments; class membership alone does not
replace their evidence or candidate indexes.

### D. Extend the supported theories and tactic matching

Proceed by separately reviewed extensions, not by assuming these are routine
consumer migrations:

1. Bitvector and integer applications, with sort/width-aware constants and
   checked interaction with offset atoms. Replace the lazy equality graph,
   64-bit adjacency map, and constant-class machinery as their roles move.
2. Algebraic constructors and pure-function applications, including
   injectivity, no-confusion, scoped binders, and the chosen finite-value
   semantics for cyclic constructor equalities. Delete the gap-74 retry.
3. Premise matching for `assumption`, `apply ... using`, and `normalize() using`
   modulo the closure of their permitted premises. `normalize() using` now
   deliberately permits the current equality graph for pointer-equality goals;
   other selected-premise operations retain their existing restrictions until
   explicitly migrated. Any restricted context must be built in work
   proportional to the selection and required term DAG.
4. Finish `rewrite`, diagnostics, and surface bridge removal using the trusted
   kernel boundary. Explanations are optional future work for a concrete
   consumer, not a requirement for certificate expansion.

Each theory extension gets its own design review, soundness negatives,
certificate/expansion checks, and scaling curves before broad migration.

## Handoff milestone

There is a substantial hard part at the front, followed by useful bounded
migration work, with further hard parts at theory boundaries.

Milestone B is the first substantial handoff point for Sol. Hand over:

- the green commit and exact gate result;
- the implemented API and invariants in the design note;
- one complete read/fold migration as an example;
- deterministic scaling and soundness regressions;
- a list of remaining consumers, their replacement API, and the old code each
  task must delete; and
- explicit escalation conditions: a task needs a new semantic rule, changes
  provenance, exposes snapshot leakage, needs global scanning, or cannot use
  the API without another alias retry.

Sol can then own a bounded stage-C migration through tests and integration.
Review the first migration before handing over a broader batch. This is an
engineering handoff based on stable interfaces and observable acceptance
criteria, not a claim that the remaining work is uniformly easy. Milestone D
and any redesign of provenance, persistence, or certificates still need
focused design review. Do not hand over "make the remaining fixtures pass" as
an undifferentiated task. No agent handoff is initiated by this document.

## Existing work and historical trial

Useful landed foundations and investigation anchors:

| Commit | Work |
|---|---|
| `7f8eac4f` | Persistent affine pointer classes and alias-fold regression |
| `9884ce02` | Specification-read retry through pointer classes |
| `56ce7b7c`, `82349436` | Centralized loaded-pointer construction/decoding |
| `69fec2b3`, `9f0efd19` | Never-address-taken and later-declared local separation |
| `387d9120` | Rewrite through a loaded pointer |
| `4ab772fa` | Historical bounded load normalizer, now replaced |
| `d80a0f32` | Historical comparison-time frame search, now removed |
| `08eb341f` | Bare-offset separation and loaded-block artifact identity |

Branch `egraph-loaded-pointer-flip`, commit `ea9de0ff`, is a historical
non-green experiment based on `08eb341f`; do not merge it. Its incomplete
decoder and quadratic `earlier_equal_load_variable` scan are not the planned
implementation. The prior handoff at `3f4386f9f` retains the full failure list
and investigation notes; the reported 16 mdtest/20 unit failures are historical,
not a fresh measurement of master or the revised design.

Useful fixture groups to revisit after a coherent representation change:
loop frame fields and two-hop descriptor reads; rewrite through loaded fields;
augment-rotate stable views; region/descriptor call framing; shared-heap parent
and detach proofs; field-derived effects; alias-store reads; artifact identity;
and ordinary verification versus expansion on the service/input-cursor examples.
Keep original C and soundness negatives. Update a test that asserts the old
encoding only when its replacement checks the new semantic invariant.

## Handoff from the DFS session (2026-09-26)

Two consumers and one soundness question for this work, found while scaling
contract entry. Nothing here changes the design constraints above.

- **Contract-entry view binding is quadratic until the closure exists.**
  `ResourceContext::view_occurrences_for_fact` (`src/kernel/primitives/resource_algebra.rs`),
  called once per view from `install_borrowed_contract_inputs`
  (`src/kernel/api.rs`), scans every candidate in the block bucket and runs a
  full `memory_range_covers` per pair, because it must refuse ambiguous
  bindings. All pointer parameters share the `ExternalArgument` block, so the
  bucket is every range. No existing key is complete for the five positive
  routes of `memory_range_covers`: constant base delta,
  `pointers_proven_equal_for_memory_resolution` (offset-equal facts, pointer
  equality paths, constant pinning), load bridging, order-derived
  containment, and `range_covered_by_fact_range`. Equality-aware address keys
  can narrow exact-address candidates, but coverage through ordering and
  containment still needs complete indexes for those relations. A permanent
  full-scan fallback would retain the scaling defect. The scaling test
  `contract_entry_with_many_views_beside_an_owner_is_not_cubic`
  (`src/surface/tests/scaling_tests.rs`) has a quadratic ceiling that should
  become near-linear when all required candidate routes are indexed; closure
  alone is not sufficient.
- **Order facts relate pointer bases inconsistently.** Under
  `requires p <= q; requires q <= p;`, the contract
  `owns p[0..1]; owns q[0..1];` is accepted at entry, while the same contract
  with `requires p == q` is refused as ambiguous. Some coverage routes read
  order facts and the partition check does not. Ordering is out of scope for
  the closure, so either antisymmetry must be excluded from equality routes
  consistently, or a proved `p <= q and q <= p` must merge `p` and `q` like any
  other proved equality. This yields no false theorem. Contract entry is
  fail-open by design: it assumes the caller, so it refuses only a proven
  overlap. Every consumer (calls, returns, folds, and refinement through
  `loans::plan_stable_view_transfer_with_bindings_and_composites`) reserves
  each owned requirement from what is actually held, and neither overlap
  detection nor coverage uses order antisymmetry, so an order-equal
  precondition is unsatisfiable. Regressions:
  `mdtests/order_equal_pointers_do_not_supply_two_owners.md`,
  `mdtests/order_equal_indices_do_not_carve_two_owners_from_one_array.md`, and
  `mdtests/a_return_cannot_produce_two_owners_of_order_equal_pointers.md`.
  The closure still has to choose between merging on proven antisymmetry and
  excluding it consistently.

## Acceptance criteria

- The intended regressions above and the milestone A/B invariants pass under
  `scripts/check.sh`; `click audit` agrees with ordinary verification and
  expansion rechecks on the integration regressions.
- The insert frontier's two case-3 leaves under a `Right` great-grandparent
  frame complete without changing the C, and `tests/examples.rs` pins the
  resulting frontier.
- Equality-aware reads, permissions, resource consumption, and selected-premise
  tactics use one consistent closure for the supported theories. Replaced
  indexes, walks, and spelling retries are deleted.
- Scaling covers relevant adversarial axes, including same-snapshot loads,
  late merges, repeated queries, and persistent branches. There is no semantic
  depth cutoff and no hidden frame search during equality comparison.
- The design note describes the built implementation, including evidence and
  provenance boundaries; concept docs explain matching modulo proved equality.
  Proofs can drop restatements whose only purpose was to reach another spelling.
