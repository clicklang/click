# Equality closure design

Status: partial implementation, 2026-09-27. Persistent affine pointer classes
now maintain same-snapshot congruence for registered opaque pointer-load blocks.
The complete pointer representation, resource indexing, and other theories
described here remain planned work.
The repository's `issues/egraph.md` owns milestones, regressions, the
handoff checklist, and historical implementation anchors.

## Current interface and trust boundary

`kernel::equality_graph::EqualityGraph` is part of the **trusted kernel**.
Its `add_equality(left, right)` operation admits an equality established in the
current proof context; `are_equal(left, right)` queries the maintained closure.
A negative query means unknown, not disequal. Insertion's return value reports
whether a class merge occurred, not validation of the supplied premise.

Pointer operations keep pointer-typed operands; `add_offset_equality` and
`are_offsets_equal` accept whole pointer-offset terms. Supported pointer-load
applications and offset terms register on demand during insertion and queries.
`add_int32_equality` and `are_int32_equal` admit and query explicit int32
equalities and their transitive closure. Further sorts and consumers will be
added in separate changes. `pointer_is_classed` and `pointer_spellings` are explicitly
pointer-specific compatibility helpers for legacy consumers.

Kernel rules may trust the graph's answers in their own proof context. There
is no `explain` API or separate derivation checker. Expanded proofs can use
simple kernel equality queries; expansion need not print the internal
congruence steps. Such a consumer must preserve the checked premises, branch,
load interpretation, and memory snapshot of the query. Cloning shares
persistent storage while keeping subsequent additions branch-local.

The larger typed-pointer migration remains an unmerged reference draft in
`codex/egraph-foundation`; this refactor imports none of its behavior changes.

`normalize() using { ... }` queries this existing graph while reducing
pointer and int32 equality conditions, including guards of conditional expressions.
Successful queries replace equality conditions with true; unsuccessful queries
leave them unknown. The same traversal handles equality leaves and nested
conditions. Graph queries may use ambient graph facts; the `using` list
restricts the additional conditions used for reduction. All cited premises must still be available and
supported. Other ambient facts, quantified bodies, and cross-snapshot frame
search remain outside this operation. Expansion retains the simple step and
rechecks it in the same proof context, without an explanation API or a
per-tactic graph rebuild. Restricted `simp() using` planning checks a
normalization candidate against only its selected context before emitting the
simple step; omitted ambient equalities do not participate in that search.
Explicit pointer-offset equalities also enter the
same graph and are available to this normalization check. This covers ordinary
C pointer parameters, which lower to offsets in a shared block, without
changing their representation.

The offset fragment interns whole terms with shallow keys and uses persistent
union-find weighted by members and parent uses. Addition signatures identify
operand classes, so equal operands establish equal sums. Indexed parent uses
propagate late merges through nested additions with an iterative worklist;
only parents of the lighter class are revisited. It preserves widths,
signedness, and machine-term snapshot identity, and adds no arithmetic solver
or cancellation rule. Queries and additions use indexed access. Existing
context restriction and equality-withdrawal rebuilds retain all graph
fragments from their remaining exact equality indexes. Ownership and framing
consumers do not query the new offset fragment.

Explicit int32 equalities use typed opaque nodes in the same term-class engine
as offsets. The graph preserves canonical machine-term identity, including
memory snapshots. Int32 scaling is a congruent application: equal indices
with the same byte width give equal offsets, and existing offset addition
applications propagate that equality. Parent-use indexes handle late scalar
merges in the same worklist. Literal indices join their folded byte constants
when multiplication fits i64. This does not infer scalar arithmetic congruence,
64-bit or mathematical-integer equality, or scalar equality from equal offsets. Exact scalar premises are counted under shallow canonical edge keys so
withdrawal preserves other premises that support the same edge. `MemoryLoad`
expressions are not separately interned for support tracking: that would allow
cross-arena snapshot comparisons to traverse unrelated memory. This is an additive consumer migration; legacy scalar reasoning outside
normalization has not changed.

## Problem and scope

A proved equality must have the same meaning at every kernel consumer.
Currently facts, cells, and loads are indexed under particular spellings, and
consumers recover different subsets of the known equalities through alias
retries, graph walks, or local normalization. The rbtree insert proof exposed
this at read permission, fold body facts, ownership consumption, and loads
after stores. Local repairs now cover some fixtures but do not establish the
general invariant.

Build one persistent equality service in the kernel, using congruence closure
without saturation. Hypotheses, checked proof steps, and execution contribute
equalities; congruence propagates them through registered applications. The
service does not invent rewrite rules or search arithmetic identities.

The first complete fragment is pointers and typed loads. Bitvector/integer
applications, algebraic constructors, and pure-function applications follow
as separately reviewed theory extensions. Ordering, general arithmetic, and
cross-snapshot frame derivation remain outside the closure. A checked theorem
from one of those procedures can contribute an equality to it.

## Semantic boundaries

### Stable names, contextual equality

Term IDs identify assumption-free syntax or an established assumption-free
canonical form. Hash-cons nodes using stable child IDs, sorts, and operator
payloads rather than repeatedly comparing deep terms. Global load naming
cannot use one proof path's equalities: the registry is shared across paths.
Two names may be distinct while their values are equal in a particular path.

Union-find state, application signatures, parent-use lists, derived class
attributes, and equality-sensitive resource indexes belong to the persistent
path context. Forking shares the prefix; adding an equality to a branch must
not change its parent or sibling. Adding equalities must never invalidate a
previous equality answer.

### Pointer values and address offsets

A loaded pointer denotes the stored value independently of the storage address
used to obtain it. Replace the current storage-relative encoding with an opaque
value identity. Constructor and decoder must change coherently: expose the
load identity/origin and any subsequent pointer displacement through a semantic
API. Consumers must not reconstruct a storage block plus scaled integer load.
Pointee width determines subsequent C pointer arithmetic, not the identity of
the pointer value just read.

The existing weighted pointer classes are useful groundwork:
`base(member) = base(representative) + delta`. Exact affine normalization can
relate displaced spellings such as `p + 8` and `(p + 4) + 4`. Preserve signedness,
bit width, wrapping, and definedness obligations of the supported C semantics;
do not distribute arithmetic through a wrapped index as if it were an
unbounded integer.

The representation must also handle same-block offset equalities and changes
to the classes of offset atoms. The current block union-find ignores equations
inside one class, so it is not the whole pointer theory. Specify how these
relations notify application and resource indexes before adopting an API.
Account for affine expression size when describing merge cost.

### Loads and memory snapshots

Model a load as an application keyed by its snapshot, address, and access
interpretation (sort/width and any other distinctions required by memory
semantics). Existing external registries may supply this information during
migration; the semantic key must be explicit in the design.

The pointer migration will use a distinct pointer-load name and an explicit
loaded-pointer block variant, rather than hiding another sort in the scalar
load-variable range. Its key is the assumption-free canonical snapshot,
address, and pointer interpretation (object-pointer value, eight-byte access).
Pointee type remains on the C value and is not key material. Live origin/epoch
metadata is separate from that defining key. The old widthless scalar load
registry can remain during this pointer phase; its mutable maximum-width field
must not decide membership in the new pointer-load application index.

Do not emit a scalar equality between a pointer-load name and a widthless
`MemoryLoad`. The pointer registry defines the pointer-valued application;
scalar bit views need their own checked conversion. A materialized pointer cell
already contains its value: reuse that value, including a retained value across
havoc only through the existing checked retention rule. Constructor, decoder,
substitution, variable collection, provenance, and rendering must all handle
the explicit loaded-pointer variant before the representation switch lands.

Equal addresses at one snapshot imply equal compatible loads. This must hold
whether the loads were registered before or after the address equality, and
whether either load already belongs to another explicit class. For example:

```text
p == q
load(M, p) == x
load(M, q) == y
----------------
x == y
```

The answer must survive extra facts and all insertion orders. Nested loads
must obey the same rule without a fixed nesting-depth limit.

Different snapshots do not become equal merely because addresses match.
Execution may preserve a load name through its existing checked unchanged-cell
rule. Additional frame reasoning belongs to explicit transport or the checked
execution rule that needs it, and contributes justified equalities to the
path. Equality comparison must not walk memory history or call a frame prover.
Do not scan all earlier loads to choose a convenient existing name.

### Provenance and separation

Value identity and proof of separation are different information. An opaque
pointer alone does not establish which allocation it can reach. Preserve
separation using evidence justified by supported C semantics, ownership, and
lifetime/reachability rules. Equal values must have consistent provenance
information, but mere inequality of term IDs proves no separation.

Do not infer a pointer's provenance from the spelling of the cell that held
it. Do not infer an allocation's birth from a contract allocation claim or
from absence in a projected snapshot. The existing special rules for hidden
locals and later-declared locals need their exact preconditions retained.
Any broader rule needs its own positive and negative tests.

Snapshots form a DAG. A proposed class attribute such as "earliest birth"
needs a semantic ordering and evidence valid in the current path; snapshot IDs
or unrelated branch timestamps do not provide that ordering. Representation
migration is not authorization to add an unreviewed provenance theory.

## Incremental closure and indexing

Maintain an application-signature table and parent-use lists alongside the
persistent equivalence relation. When child classes merge, reconsider affected
parent applications, merge signature collisions, and continue until the pending
work is complete. Queries may register their explicit terms, but must observe
a closed state before returning. Batching is allowed only if it preserves this
boundary and charges the actual maintenance work.

The initial `PointerClasses::normal` recursively normalized loads with a depth
cap and a same-snapshot scan. It has been replaced. `PointerClassState` stores
load applications, block use lists, application signatures, and reverse
signature bindings. Registration walks only a query's unregistered load-address
dependencies; merges reindex users of moved blocks and enqueue colliding load
values for merging. Every registration/merge drains the worklist before return.
Class weight counts blocks and application uses, so high-fanout classes remain
on the heavy side of a merge. A context clone copies persistent roots into its
own lock; query registration cannot mutate a sibling's closure.

Signature keys contain snapshot arena identity, representative block identity,
and an affine-offset ID. Offset sequences are interned with shallow prefix keys
and retained machine-atom IDs. This removes deep snapshot/term comparison from
signature lookup. Explicit affine syntax is normalized with an iterative walk;
legacy spelling output sorts structurally rather than by interning order.
The existing weighted affine payload operations still need broader scaling
review for growing symbolic deltas. Same-block equations and equality between
offset atoms are not yet incorporated into this closure.

Only registered pointer-width loads in opaque symbolic-block form enter this
application index. Ordinary C load construction still uses the old encoding in
some producers. This is a preparatory fragment, not completion of the coherent
representation change or the read/fold integration milestone.

Resource lookup needs indexed equality-aware addresses, including displacement.
Specify how resources registered before a merge remain discoverable after the
representative changes. Resolving a query's ID with `find` alone does not move
entries still stored under an old representative. Possible implementations
include persistent per-class payload indexes merged by size, or explicit
reindexing of affected entries; choose and measure one in the foundation.

Read and fold consumers are the first integration examples. A lookup must not
enumerate every spelling in a class. Equality indexing narrows candidates;
permission quantities, range containment, ownership reservation, and ordering
still require their own checked judgments and complete candidate indexes.

## Persistence and cost

Follow the [verification-efficiency contract](verification-efficiency.md):
explicit checking is approximately linear up to logarithmic indexing factors
in the selected source, proof, and required output. Incremental closure is a
proposed means to meet that contract, not a blanket complexity guarantee.

In particular, measure signature maintenance, persistent map updates, affine
payloads, explanation construction, resource reindexing, and repeated branch
extensions. Do not claim a whole-verifier bound from union-by-size alone.
Avoid whole-state clones, deep structural cache keys, repeated same-snapshot
load scans, and alias enumeration on each resource access.

Restricted contexts rebuild from the selected premises and required term DAG.
They must not inherit ambient merges or explanations. Fact withdrawal likewise
must invalidate every consequence that depended on the withdrawn fact; either
rebuild the affected context under a documented bound or use a justified
persistent strategy. Execution writes do not withdraw facts about old snapshots.

Deterministic regressions vary multiple input sizes along these axes:

- chains, balanced merges, late merges, and repeated equality queries;
- nested loads and many unrelated loads within one snapshot;
- repeated loads across a growing store history;
- resource lookup through growing classes and resources present before merges;
- many branches extending a large common prefix; and
- restricted contexts beside growing unrelated ambient facts.

Count total work as well as query work so moving a scan from query to insertion
does not hide it. Ordinary verification must pass before profiling or expansion.

## Evidence and trust

The closure is a kernel decision procedure. Every non-definitional merge must
have a checked source: an admitted hypothesis, an execution rule, another
checked derivation, or a congruence/theory consequence of such sources.
Certificates and selected-premise tactics must use only their allowed context.
The graph itself is trusted; a kernel equality query does not require a
separate explanation or derivation checker. A future explanation facility
would need a concrete consumer, such as diagnostics or premise dependency
reporting. It is not a prerequisite for `click expand`: a simple checked
operation can query the graph maintained from the certificate's allowed facts.

Equality substitution now has a kernel-owned checked rule in
`proof/equality_rewrite.rs`. It admits the cited equality through the persistent
exact premise index, computes the substitution, and returns a private checked
result. That result constructs the proposition obligation; surface code supplies
presentation data, not a replacement semantic goal. A different load spelling
must pass the kernel's corresponding-leaf transport check first. The candidate
helper used by smart planning has no proof authority.

The outer quantifier walk refuses binder collisions with the bounded,
carrier-aware variable collector, which treats snapshots as opaque. Direct
regressions cover unavailable/reversed premises, sibling-context isolation,
forged presentation, shadowing, capture, and ambient premise/snapshot scaling.
Source-level exploit reachability was not established. Goal lowering/unfolding
and other transitions through the generic publisher remain separate trust
boundaries; they were not migrated by extracting this equality rule.

Soundness tests include unproved aliases, snapshot changes, incompatible load
interpretations, branch leakage, restricted-premise leakage, offset wrapping,
and tampered equality explanations. Later constructor support must address
injectivity, no-confusion, and cyclic equations under the declared value
semantics. Distinct constants of the same sort produce a contradiction;
constants in different sorts must not be merged at all.

## Migration and deletion

The issue defines four milestones: contract/regressions, integrated pointer/load
foundation, remaining pointer consumers, then theory/tactic extensions. The
historical non-green loaded-pointer trial is evidence about dependencies, not
the implementation plan. Use isolated worktrees and integrate only coherent
green commits. Preserve the original C regressions.

Delete old mechanisms as their responsibilities migrate:

| Responsibility | Mechanisms to retire |
|---|---|
| Pointer equality and permission lookup | Alias indexes, equality walks, `pointer_spellings`, `resolve_symbolic_pointer_alias` |
| Load identity/equality | Minted-load scans, recursive load normalizer, comparison-time frame search, spelling retries |
| Scalar equality | Lazy bitvector graph, 64-bit adjacency map, `ConstantClasses`, exact constant aliases |
| Algebraic/function congruence | Gap-74 alias retry and duplicated operand-wise equality recursion |
| Tactic matching | Surface bridges made redundant by checked closure queries |

An intermediate consumer may retain its legacy implementation until migrated,
but a migrated consumer must not quietly fall back to a second equality
relation. Full deletion is an acceptance criterion, not optional cleanup.

The first substantial handoff is after the pointer/load representation and
closure work through real read/fold consumers, with checked evidence, scaling
regressions, and the full gate passing. That creates bounded consumer migrations
against stable APIs. Bitvectors, algebraic terms, provenance changes, and
certificate changes still require design review when reached.
