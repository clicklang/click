# Equality closure design

Status: partial implementation, 2026-09-30. The trusted persistent graph
maintains affine pointer classes, offset and int32 congruence, and registered
same-snapshot pointer and four-byte scalar loads. Selected normalization,
transport, memory, resource-value, and range consumers query it. Ordinary C
pointer loads still have a storage-relative representation; equality-aware
resource indexing is implemented for selected consumers. Other theories
described here remain possible future work.
The repository's `issues/egraph.md` tracks only the P1 pointer-read and
read/fold behavior needed by the rbtree proof. The wider design in this note
is reference material, not additional P1 acceptance criteria.

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
equalities, addition congruence, and registered same-snapshot int32 load congruence. Further sorts and consumers will be
added in separate changes. `pointer_is_classed` and `pointer_spellings` are explicitly
pointer-specific compatibility helpers for legacy consumers.

Kernel consumers use `PureFactContext::pointers_known_equal(left, right)`
for equality already established by this trusted graph. It neither searches
arithmetic facts nor walks an alias component. `false` means unknown.
`pointers_proven_equal_by_reasoning` names the broader arithmetic/condition
judgment; `pointers_proven_equal_for_memory_resolution` retains structural
object-distinctness and explicit resource-separation guards. A graph answer
alone supplies no memory access authority.

Kernel rules may trust the graph's answers in their own proof context. There
is no `explain` API or separate derivation checker. Expanded proofs can use
simple kernel equality queries; expansion need not print the internal
congruence steps. Such a consumer must preserve the checked premises, branch,
load interpretation, and memory snapshot of the query. Cloning shares
persistent storage while keeping subsequent additions branch-local.

The larger typed-pointer migration remains an unmerged historical reference
draft in `codex/egraph-foundation`; its behavior changes are not on `master`.

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
union-find weighted by members and parent uses. Its query first recognizes
exact affine-equivalent byte offsets, including regrouped or reordered sums
without a premise. `simp` uses that query for same-block pointer conditions,
which lower to offset equality. Addition signatures identify operand classes,
so equal operands establish equal sums. Indexed parent uses
propagate late merges through nested additions with an iterative worklist;
parents of the lighter class are revisited. When a class first acquires a
literal value, its existing parents also receive constant evaluation. It preserves widths,
signedness, and machine-term snapshot identity, and adds no arithmetic solver
or cancellation rule. Queries and additions use indexed access. Existing
context restriction and equality-withdrawal rebuilds retain all graph
fragments from their remaining exact equality indexes. The pointer query
compares affine coordinates and whole offset classes inside the graph. Same-block pointer premises also join whole offsets.
Equal-base and representable constant-displacement queries use direct offset
class lookups, including either translated spelling. At an unclassed ordinary
base with no offset merges, the known-equality query stops after reflexivity;
explicit offset normalization remains available through `are_offsets_equal`.
This avoids normalization work during unrelated field-separation checks.
These checks require no alias enumeration or cancellation rule.

When a checked cross-block pointer premise has a symbolic displacement that
cannot be spelled as an offset term, the graph additionally joins its raw
`address(block, offset)` applications. Offset-class merges then propagate by
ordinary congruence, so `x == y`, `address(A, y) == z`, and `z == null` establish
`address(A, x) == null` in any insertion order. Affine block merges translate
registered applications when that translation is spellable. Query registration
can use a stated `i64::MIN` translation directly without constructing its
opposite sign. Unsupported translations otherwise remain unknown.
Raw applications supplement the affine fragment only where its offset
spelling loses this connection; derived load merges retain their existing
indexed closure rather than eagerly duplicating every application.

Explicit int32 equalities use typed nodes in the same term-class engine
as offsets. Int32 addition has its own application signature and shallow child
IDs; other scalar operations remain opaque. Equal operands give equal sums,
including late equalities and nested additions. Registration canonicalizes each
input once before walking its supported constructors. Literal sums use the
kernel bitvector wrapping semantics; equality does not prove C signed
definedness. No commutativity, cancellation, or arithmetic solver is added. The graph preserves canonical machine-term identity, including
memory snapshots. Int32 scaling is a congruent application: equal indices
with the same byte width give equal offsets, and existing offset addition
applications propagate that equality. Parent-use indexes handle late scalar
merges in the same worklist. Literal indices join their folded byte constants
when multiplication fits i64. This does not infer congruence for other scalar operations,
64-bit or mathematical-integer equality, or general injectivity of offset constructors. Exact scalar premises are counted under shallow canonical edge keys so
withdrawal preserves other premises that support the same edge. `MemoryLoad`
expressions are not separately interned for support tracking: that would allow
cross-arena snapshot comparisons to traverse unrelated memory. This is an
additive consumer migration.

True offset premises also feed the shared graph through the existing checked
int32 element-index interpretation: four-byte scaling, aligned constants, and
supported additions. Equal byte offsets then imply equal int32 index residues.
This premise translation shares support counting with explicit scalar edges;
withdrawing one premise retains any other support for that edge. It does not
infer exact offset equality from equal wrapping residues.

`PureFactContext::int32_values_known_equal(left, right)` is the shared query
for wrapping int32 value equality in the trusted graph. It replaces the old
Boolean fact-component walk and its separate memo. Condition decisions,
transport, resource matching, and memory consumers use the same maintained
closure, including addition, literal evaluation, and registered load
congruence. Queries do not build the legacy condition-fact index; deterministic
regressions check bounded cold query work beside increasing equality classes
and unrelated facts, as well as late merges and persistent branch isolation.
Opaque operands use existing-node lookups. An absent nonliteral opaque
endpoint cannot be produced by constructor registration, so such a miss stops
without interning unrelated applications. Supported additions and registered
loads still register when congruence or literal evaluation can establish equality.
Representative lookups use a disposable node-ID cache guarded by the merge
history's epoch. Unions invalidate entries lazily; forks start an empty local
cache in constant work, while semantic graph storage remains persistent.
There is at most one cached representative per node, with no term-pair cache
or deep structural key.

Residue equality remains distinct from exact byte-offset equality. Memory
resolution checks that both rebuilt indices are exact before a positive
residue equality can prove an offset equality; unequal residues can still
refute one. `wrapped_index_sum_does_not_decide_pointer_offsets_equal` and
direct memory-resolution regressions protect this boundary across element
widths. Resolved-load value comparisons require a recorded four-byte read;
a byte, short, or wide read cannot acquire int32 semantics by resolving its
stored term. The general memory and expression reasoning APIs still perform
their explicit checked judgments; the known-value query does no arithmetic
search or snapshot transport.

The lazy exact-equality index remains for consumers that enumerate aliases or
produce premise-path evidence. Those are distinct operations, not a second
Boolean equality checker. This chunk does not migrate the 64-bit adjacency
index, mathematical-integer equality, or constant discovery.

The central memory resolver now asks pointer classes for cross-block equality
and offset classes for exact same-block byte-offset equality. Its pointer
query still rejects structurally distinct blocks and explicitly separated
ranges; its offset query still treats equal wrapping int32 residues as
insufficient unless the existing exact-index rebuild check succeeds. A graph
offset edge can flow
through int32 scaling and offset addition into a pointer address without
building the legacy scalar fact index. Context forks, fact withdrawal, and
restriction keep these answers scoped to their supporting premises. Broader
memory arithmetic and framing rules remain in the resolver.

The simple pointer-equality decision now uses typed graph queries only. It no
longer scans all ambient condition facts for a matching translated equality
or walks their alias component. Overflow-guarded translation such as
`p == arr + i` after incrementing `p` and `i` instead uses an explicit
`arithmetic() using` proof with the entry pointer relation and strict index
bound. A displaced cross-block query now uses an exact translated offset edge
only for a representable constant base displacement. Symbolic displacements
can remain unknown until a checked proof supplies the translated equality.

The memory-separation reader uses the same known-equality query. The
superseded Boolean alias-component walk has been deleted. Exact alias indexes
remain for evidence-producing enumeration and other consumers; their presence
does not imply a second Boolean pointer-equality system. Deterministic tests
cover mixed offset/block chains, all premise insertion orders, late offset
merges, branch isolation, and bounded query work beside growing offset classes.

The full and shallow `Bitvector32Equal` decisions use the shared known-value
query. Explicit negative premises, arithmetic rules, and checked memory
resolution remain separate. Int32 fact transport uses the same query before
its structural and broader expression rules; it has no separate Boolean
fact-path fallback. Exact pointer-offset decisions retain their no-wrap guard.

The commutative int32-addition matcher also queries the graph when comparing
individual addends. A reordered sum can therefore use registered load
congruence or a joined scalar class even though the graph does not itself
reorder addition. Other checked addend rules still cover forms outside this graph fragment.

Direct memory-resource matching now queries graph equality for its int32 range
start and end values through the shared known-value query. These fields are
scalar values, not byte-offset equivalences; the resource base still follows
its separate pointer check. Congruent sums and registered same-snapshot loads
can therefore identify equal range endpoints, while changed snapshots and
withdrawn premises remain distinct.

The checked `CValue::Int32` value comparison now queries the graph before its
broader memory-resolution path. Direct composite, token, and instance matching
use that shared typed rule for resource arguments and instance fields, rather
than maintaining a resource-specific graph check. Byte-typed values and pointer
arguments retain their separate rules. Registered loads in one snapshot may
match as values, while changed snapshots and withdrawn premises do not.
Multi-size regressions check that graph matches avoid building the legacy fact
index.

Contract certification's `Bitvector32Equal` check now uses this typed int32
value rule after its checked cross-snapshot load rule. Graph-congruent sums and
same-snapshot loads therefore certify without searching the legacy fact index;
changed snapshots and withdrawn premises still fail. This affects scalar
equality claims, not pointer-offset certification.

Certification of call- and loop-havoc mutable-range lists now uses the typed
int32 value rule for each start and end, after separate width and pointer-base
checks. The general range-endpoint helper also serves scaled pointer offsets;
it has not been changed to accept wrapping graph equality as exact address
equality. Regressions cover same-snapshot loads, changed snapshots, withdrawn
premises, width mismatch, and multi-size queries without the legacy fact index.

The structural, memory-resolution, and covering-span loadable-range readers
now share one typed int32 value rule for matching byte extents at the same
base. Their callers retain the range-availability check for the goal snapshot;
equal extents do not supply viewability by themselves. Tests retain the
loadable-premise and base boundaries and check direct multi-size queries
without the legacy fact index.

Same-base range containment now uses the typed int32 value rule when its
signed endpoint-order check has equal operands. Equal endpoint bitpatterns
establish `<=`; this does not infer an exact byte-offset difference from a
wrapping scalar equality. Other order and containment rules remain separate.

When a signed-order fact is found by one exact endpoint, its other int32
endpoint is compared through the graph first. The containment order check
tries these indexed facts before its broader scalar equality fallback, so a
graph-congruent match does not build the legacy fact-path index. Candidate
lookup still requires one syntactic or canonical endpoint key; it does not
search every order fact for a graph-equivalent endpoint.

The kernel comparison of condition facts for certified transport now uses the
typed int32 value rule for operands of matching signed-order or equality
conditions. Condition kind and truth value must still match. Registered loads
remain scoped to their defining snapshot, and withdrawn premises lose their
consequences. Multi-size queries avoid the legacy fact index.

Allocation continuity across a call now compares its two 32-bit size values
through the typed graph rule after the separate allocation-base check. This
does not use wrapping value equality to establish pointer-base equality.
Regressions cover same-snapshot loads, overwrite and withdrawal boundaries,
different bases, and multi-size graph queries without the legacy fact index.

After indexed resource matching misses, the zero-ownership fallback now uses
the typed int32 graph rule for the required quantity. This is value equality
with zero, not a resource-key or pointer match. Regressions cover graph-
congruent registered loads, changed snapshots, withdrawn premises, and
multi-size zero-quantity queries without the legacy fact index.

For a range pair already selected for composition, endpoint comparison uses
the graph-backed int32 condition decision. The composition helper no longer
repeats a separate legacy fact-path walk after that decision. Candidate
selection remains its own index boundary: normalization does not yet discover
every pair whose endpoints become equal only through graph congruence.

After the existing memory resolver establishes a four-byte scalar load's
value, load equality compares it through the shared int32 query. Resolution still supplies the value in the
load's snapshot; graph equality neither resolves stores nor grants read or
frame permission. Other load widths keep their existing comparison path.
Regressions cover both comparison directions, a changed snapshot, withdrawn
premises, a one-byte load, and multi-size query work.

When both operands are resolved four-byte loads, the same path compares their
checked stored values through the same graph query. Neither load's opaque name needs to equal the other load's stored term.
Each value still comes from its own recorded snapshot. Changed or withdrawn
evidence and a resolved one-byte read do not use this two-load rule.

Registered four-byte scalar loads also participate as int32 applications. Their
signature contains the registered defining snapshot's arena identity, the exact
storage block, and the offset class. Equal offsets therefore give equal reads
in that snapshot, including when the offset equality arrives later. Load
registration follows nested index dependencies iteratively; merge propagation
uses the same parent-use index as addition and scaling. Neither step scans
unrelated snapshots or enumerates address spellings.

The defining snapshot can already be an assumption-free canonical projection.
The graph uses that registered definition, never the mutable live origin. It
does not equate distinct defining snapshots or storage blocks, search for frame
evidence, resolve stores, or grant read permission. Unregistered, unknown-width,
and other-width loads remain opaque. Existing canonicalization can independently
retain a value across a justified memory change; this slice adds no new rule
for doing so. Global load naming remains independent of contextual equality.

Checked transport conclusions enter the ordinary int32 equality interface.
For example, after a store to `p[k]`, explicit transport can use `i != k` to
prove that `p[i]` equals its entry value. With `i == j`, normalization then
combines this edge with current-snapshot load congruence to prove the same for
`p[j]`. The graph needs no frame search or snapshot-merging operation.
[The executable composition example](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_transported_int32_loads.md)
keeps the transport and graph steps explicit. Regression tests remove either
premise or the bridge, reject an overlapping store, recheck expansion, and
verify that withdrawing the bridge removes only its cross-snapshot consequences.

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

A typed pointer-load application in the equality graph denotes the stored
value independently of the storage address spelling and pointee width. The
graph can answer equality of two such applications without replacing the
`Pointer` values produced by C execution. A live caller must supply the actual
defining snapshot and address from a typed load site or checked evidence; the
storage-relative `Pointer::as_loaded` shape also describes indexed pointer
arithmetic and is not sufficient evidence by itself.

The bridge from a completed nonvolatile C pointer read to the graph
application is execution evidence scoped to that path. The typed producer
registers its value with the exact defining snapshot and address; only a
matching defining equation in the path's fact context files the equality in
the graph. It is not published as an ordinary proposition premise: doing so
changes a statement theorem from `Executes` to `bridge => Executes` and makes
resource child-argument checking reject previously readable expressions. The
graph relation changes neither logical premises nor read permission. Volatile
reads do not register this bridge.

Specification pointer loads now retain an exact definition supplied by their
typed producer as graph term metadata. These definitions are shared across
contexts within one verification session, like load-variable interning;
address hypotheses, unions, and their consequences remain in persistent
path-local graph roots. Reconstructing a context must not forget what a logical
term denotes. Registration never decodes arbitrary pointer arithmetic and adds
no proposition premise, ownership, read validity, or cross-snapshot equality.
Each query registers only its named values and their recorded dependencies.
A registration generation distinguishes reasoning memo entries from earlier
misses, without scanning or rebuilding the proof environment. `simp` can emit
`normalize() using {}` to check an equality against this ambient graph.
The nonrecursive `mdtests/egraph_resource_pointer_load_alias.md` regression
checks this after an unfold publishes address equality.

Recursive resource child indices use the same term-definition interface.
After a child expression passes the existing readable-expression and argument
checks, its certified typed producer metadata is retained before the temporary
fact stream is discarded. The cached scalar-cell conversion preserves this
metadata just as the symbolic pointer-read route does. Ordinary propositions
and volatile reads cannot supply it. `mdtests/egraph_recursive_child_alias.md`
checks unfold at one parent spelling and fold at an equal model identity,
without intermediate field-load claims or C writes. This does not transport
loads across different snapshots.


The kernel now has a distinct `PointerLoadId`, `PointerBlock::LoadedPointer`,
and a constructor/decoder pair for `(defining snapshot, address, displacement)`.
The equality graph indexes this explicit pointer application without consulting
the scalar load registry's mutable access width. Ordinary C pointer-load
producers still create the storage-relative form; their checked path-context
bridges relate that form to the explicit graph term. Making the explicit name
the execution value is a separate proposal that would require a coherent
review of materialization, substitution, provenance, and rendering. Merely
swapping the constructor breaks existing verification and expansion fixtures.

The existing weighted pointer classes are useful groundwork:
`base(member) = base(representative) + delta`. Exact affine normalization can
relate displaced spellings such as `p + 8` and `(p + 4) + 4`. Preserve signedness,
bit width, wrapping, and definedness obligations of the supported C semantics;
do not distribute arithmetic through a wrapped index as if it were an
unbounded integer.

The graph now records an exact offset equality when a congruence merge joins
two pointers already in one block class. Further changes to offset-atom
classes still need a reviewed notification path into application and resource
indexes. Account for affine expression size when describing merge cost.

### Loads and memory snapshots

Model a load as an application keyed by its snapshot, address, and access
interpretation (sort/width and any other distinctions required by memory
semantics). Existing external registries may supply this information during
migration; the semantic key must be explicit in the design.

The typed graph query uses a distinct pointer-load name and an explicit
loaded-pointer block variant, rather than hiding another sort in the scalar
load-variable range. Its key is the assumption-free canonical snapshot,
address, and pointer interpretation (object-pointer value, eight-byte access).
Pointee type remains on the C value and is not key material. Live origin/epoch
metadata is separate from that defining key. The old widthless scalar load
registry can remain during this pointer phase; its mutable maximum-width field
must not decide membership in the new pointer-load application index.

Do not emit a scalar equality between a pointer-load name and a widthless
`MemoryLoad`. The pointer registry defines the graph application;
scalar bit views need their own checked conversion. A materialized pointer cell
already contains its value: reuse that value, including a retained value across
havoc only through the existing checked retention rule. If a future change
uses the graph's explicit loaded-pointer node as the C execution value, its
constructor, decoder, substitution, provenance, and rendering consumers must
be reviewed together. The current equality query requires none of that.

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

Registered pointer-width loads in opaque symbolic-block form enter this
application index. Ordinary C load construction retains its existing encoding;
checked read-site equations connect its values to the graph's applications.
Pointer comparison uses that closure directly. Read/fold resource indexing
has its own ownership and range-coverage boundaries below.

Resource lookup now pairs persistent resource roots with the trusted graph's
pointer-class merge stream. Memory facts have a raw block/affine-base index
maintained at insertion and removal, so a cold lookup can pair that index
without scanning the resource store. The initial execution proof boundary
registers the selected resource input's starts as typed graph address
applications. Successors register only newly published occurrences. A paired snapshot retains both resource and graph checkpoints;
execution proof-step boundaries advance it using exact occurrence deltas and
class merges. Forks share those roots and have independent cache locks.
A restricted or sibling context starts from raw roots and its own graph's
merge stream, rather than retaining unsupported address associations.

Each class has a persistent affine-address bucket. Its coordinate origin may
differ from the graph's representative: a merge keeps the larger **resource
payload** and shifts only the smaller payload, even if the graph's block/use
weight chooses the other representative. This avoids repeatedly rekeying a
large resource bucket when it acquires resource-free aliases. Queries select
symbolic ranges at the requested affine base, or concrete spans selected by
their canonical starts (including the predecessor and starts inside the
requested span). The resource algebra then checks access mode, quantity and bounds; an indexed equality grants no
ownership. Full resource normalization refreshes the derived payload during
its existing complete-input operation because normalization can renumber entry
IDs; ordinary deltas do not rebuild it or scan exact-fact buckets.

Fold consumption uses this paired address/span index instead of enumerating
pointer spellings. A selected candidate can express the requirement in its
own block coordinates using the graph's affine relation; this visits no other
class members. Existing local range matching remains responsible for
same-block containment and endpoint reasoning. Specification reads also use
the paired index for concrete affine addresses in classes whose memory entries
all have positive concrete read cores. A persistent AVL interval tree stores
each occurrence's byte start/end and each subtree's maximum end. It lazily
selects ranges covering the access's candidate footprint, including mixed extents and overlapping
views where the nearest predecessor is too short. A read stops at the first
candidate accepted by the ordinary permission and bounds checks; it does not
materialize every overlapping view. Updates copy only the affected tree path,
and class merges shift only the smaller resource payload's interval tree.
The occurrence count detects incomplete index coverage and selects the general
checker before lookup; an indexed miss is final. This avoids scanning unrelated
ranges for both hits and misses, including resources published before a later
address equality. Reads outside that fragment retain the general checker.
Whole-cell read hits also use an exact-start payload attached to typed graph
address classes. Offset congruence and late same-snapshot loaded-pointer
merges update this payload through the graph's persistent term-merge stream.
Block merges translate only affected registered address applications. Payload
unions retain the larger entry set, even when the graph chooses the other root.
Raw offsets and their affine normal forms are definitionally connected inside
the trusted graph; this registers no proposition or ownership premise.

Each exact-start class indexes eligible occurrences by authorized read
footprint. A known equality selects only entries of the requested footprint;
different or unsupported read shapes at that address or elsewhere in the block
class do not disable the match. Registration, removal and class merging update
both the complete fold-candidate set and these read sets. Each occurrence
contributes at most two footprints (including the logical pointer-slot rule),
and merges move both indexes from the smaller occurrence payload. Input
registration still belongs to the execution proof boundary. An unbound class
is unknown: scalar arithmetic or snapshot transport may justify an equality
outside this closure, so that case retains the existing general checker. Candidate delivery is lazy; equality selects the
occurrence's own start and the ordinary checker still validates its quantity,
access mode, and bounds. The logical four-byte pointer-slot convention remains
unchanged, including interior reads of longer int32 ranges, which cannot use
the whole-cell path. Unrelated scalar equality no longer disables this cell
fragment. The same address payload supplies fold candidates, whose coverage
and consumption checks remain authoritative. Cold lookups cannot trigger full
input registration; they retain the existing affine/general paths until a
proof boundary establishes complete coverage. Branches inherit registered
persistent roots. Divergent registration prefixes cannot reuse branch-local
node IDs. Queries on temporary contexts fork the index roots so they cannot
replace the source graph's published input checkpoint. Queries on that source
advance the memo checkpoint, avoiding repeated accumulated deltas. Full
normalization defers its published registration delta to the source graph
rather than altering a private graph checkpoint.

Symbolic containment, partial-range reads with non-affine offset aliases, and
snapshot-based matching still need complete indexed coverage before the
general read lookup can be retired. The interval summary is part of the trusted kernel's derived index;
it creates no proposition or access capability.
Candidate footprint calculation shares the kernel's existing logical
pointer-cell rule: a pointer read may use one 4-byte logical element, while
other element widths still need their own full range check. The index must not
silently tighten that rule to physical pointer width during this migration.
Deterministic regressions cover late aliases,
nonzero displacement, branch isolation, insertion/removal and normalization,
growing alias classes, disjoint spans sharing one base, concrete read hits and
misses, mixed extents, overlapping views, lazy delivery of covering ranges,
interval updates against an independent model, and incremental merges
with a large resource payload. Resource-section publication uses the expansion
delta rather than recreating views for unrelated ambient memory ranges.

Write-resource candidate selection now shares the complete affine interval
summary. It selects covering occurrences lazily, translates the access into
each owner's block through checked graph equality, then applies the existing
write-permission and bounds judgment. Views cannot supply write authority.
An indexed miss or failed candidate check is decisive for this covered
fragment; it does not retry spellings or scan the remaining resources.
Whole-cell read payloads are not used for writes: an exact-size view can
coexist with a larger covering owner. Symbolic, non-affine, loaded-pointer,
and incomplete interval shapes still select the general write lookup before
checking candidates. Retiring that remaining path requires a separate
complete write-candidate index for those shapes. The existing logical
pointer-cell width rule is preserved for both access judgments.

Read, write, and fold consumers are integration examples. A lookup must not
enumerate every spelling in a class. Equality indexing narrows candidates;
permission quantities, range containment, ownership reservation, and ordering
still require their own checked judgments and complete candidate indexes.

## Checked pointer-read sources

Typed pointer-read producers now share `PureFactContext::register_pointer_read`.
It records the existing value's load definition and, when the exact defining
snapshot (or its recorded canonical projection source) is a `CellsSeeded`
edge supplying the entire read footprint, admits equality with that run's
source read into the branch's graph. Only load-valued, contiguous, live slots
of the required width qualify. The check inspects the selected slots rather
than the run's extent, address aliases, or snapshot history. Canonical
projection bridges use exact producer registry entries. These are trusted
kernel rules; they introduce neither proposition premises nor access rights.

Ordinary pointer equality queries and resource consumers use the resulting
closure. A later address equality propagates through the registered source
applications without repeating this check. There is no special comparison
rule in `fold`. Producer publication occurs only after a typed read's existing
prerequisites have been checked. The graph's generation invalidates equality
misses recorded before publication; persistent sibling contexts retain their
own admitted unions.

The same producer boundary now handles one immediate `Store` edge. It uses
structural object separation or an exact constant byte gap, after re-expressing
the selected read in the store's block through established graph equality.
It checks the store's full value width against the read footprint and admits
`load(after, address) == load(before, address)` only when their bytes are
separate. The exact byte geometry is shared with the memory checker. It does
not use address inequality alone, scan ownership frames, or walk older memory.
Already admitted single-store edges compose through ordinary graph closure;
unknown store-address aliases require a later producer check once the needed
separation is available. Unregistered intermediate edges remain unknown.

Snapshot producers also maintain an immutable **read identity** for graph
load congruence. A recorded `CellsForgotten` edge inherits its base's identity:
removing cached knowledge changes no program bytes. A load-valued `CellsSeeded`
run inherits it only when the run's source and base already share that identity
and each slot's stride equals its value width. Copying the same bytes already
in the base is materialization, including successive sibling runs copied from
an equivalent earlier snapshot. Other transitions receive a distinct identity.
The pointer and int32 graph-load signatures use this key while the existing
load terms and C pointer values retain their original snapshot representation.

This metadata is part of the trusted kernel and establishes value equality
only. It does not establish snapshot equality, read permission, initialization,
allocation continuity, or framing. Unrecorded pruning, constant or symbolic
storage runs, changed sources, stores, and havoc cannot inherit a key by this
rule. Checked separate-store unions still belong to their proof branch.

The key is fixed at first interning. If a snapshot was already interned without
this annotation, recording a later edge conservatively loses the new equality;
existing graph applications never require relabeling or rescanning. Arena reset
keeps prior-session keys distinct. Production uses immediate-source key lookups
and does not enumerate slots or registered reads. Endpoint queries compose
arbitrarily many already-produced materialization/forgetting transitions with
ordinary congruence, without intermediate read publication or a history walk.
Deterministic regressions check approximately linear production over increasing
histories and constant endpoint-query work. The redundant per-read forgetting
admission rule has been removed.

The recursive unfold → sibling-field write → refold fixture now verifies,
expands, and independently rechecks. Overwriting the pointer field instead
rejects the expanded proof.

A retained cell-map entry alone is insufficient preservation evidence:
low-level snapshot construction can leave it present after a write through a
possibly aliasing address. Other memory transitions and separation forms
remain future work at this common kernel boundary. Deterministic tests cover
late read-address aliases and transitivity, complete and incomplete footprints,
changed and unknown writes, branch isolation, increasing runs and alias
classes, constant work beside increasing unregistered store histories, and
approximately linear composition of published store edges. The ordinary
single-store Click claim expands and independently rechecks; changing its C
write to overwrite the pointer field rejects the expanded proof.

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

Int32 Boolean consumers now share one graph query. Exact alias enumeration,
premise evidence, constant discovery, and wider scalar theories still retain
their own indexes. For each further consumer migration,
identify the remaining fallback cases, cover them with the intended checked
judgment, and delete the superseded path. Full deletion is an acceptance
criterion, not optional cleanup.

The first substantial handoff is after the pointer/load representation and
closure work through real read/fold consumers, with checked evidence, scaling
regressions, and the full gate passing. That creates bounded consumer migrations
against stable APIs. Bitvectors, algebraic terms, provenance changes, and
certificate changes still require design review when reached.
