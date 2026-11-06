# Unspellable facts: shared kernel terms and total Surface spelling

Priority: P1.

Soundness: incomplete. No false acceptance is known from a missing spelling.
A fact or goal that cannot be written loses proof completeness, prevents checked
expansion, or produces a placeholder. Removing a compatibility checker without
preserving its proof rules also loses completeness and is not a valid migration.

## Goal and invariants

Every fact and goal held by a proof state has Surface syntax satisfying
`lower(raise(x)) == x`. `SurfaceTerm` represents source expressions;
`KernelTerm` is the common typed immutable expression DAG. Source-to-kernel
lowering can make implicit conversions explicit, so the reverse round trip is
canonicalization, not preservation of every original source spelling.

- Lowering is structural and fact-stable. Facts may discharge obligations or
  establish equalities; they must not choose or simplify the constructed term.
  Equalities belong in the equality graph or comparison form.
- Definedness is a separately scoped obligation expressed with ordinary
  propositions, discharged by ordinary proof checking. Do not put guards back
  into lowered values or add a final certification recheck.
- Existentials require a defined, true chosen witness; their negation requires
  every candidate to be defined and false. Universals require every candidate
  to be defined and true; their negation requires a defined, false witness.
- Stepping through n statements stays near linear. Shared arithmetic must not
  become a boxed tree at each prefix. Adding indexed equalities is allowed
  when discovering the addition is cheap.
- Each step decides its frame from the preceding state. Record supported frame
  equalities there; do not repeatedly search old states or add fact-aware
  fallbacks to individual checks.
- Name values and effect points when introduced. Calls retain `.result`,
  including discarded results; heap identities have `.allocation`. Historical
  facts retain their state names.

The authoritative rule and audit commands are in
[Spellability](../docs/internals/spellability.md). Related frame work is in
[fact-aware-frame-walks.md](fact-aware-frame-walks.md).

## Current position

The common types, structural constructors, shared machine arithmetic storage,
scoped ordinary definedness propositions, and many checker operand views exist.
They do not yet replace every legacy kernel representation. `ContractExpression`
remains a compatibility alias for `SurfaceTerm`; unmigrated payloads and checker
adapters remain explicit migration boundaries.

Merged checkpoints relevant to the active work:

- #2192 introduced the common types and structural DAG.
- #2309 migrated operation/range and quantified bridges and interval sources.
- #2325 retained shared operands in selected bound consumers.
- #2328 migrated native comparison-class queries and variable-chain matching.
- #2330 migrated signed 32-bit ranges, constant-offset definedness decisions,
  and comparisons whose operands are pinned by equalities.
- #2331 added spelling for borrowed Rust enum/type-parameter locals and
  algebraic call results. Held locals lower to their versioned object reads;
  historical reads use `at(point, o)` and call results use `<region>.result`.

Endpoint-bound helpers and the exact signed-order walk now consume operand
views (#2333). Wide constant evaluation, wide order-chain endpoints, constant
comparison decisions, and signed-64 interval entry points also consume views
(#2337). Wide equality sources retain their original propositions in an endpoint
index, so implicit reasoning can cite a shared equality without exporting its
operands.

Ordinary ring-operation domain decisions consume `OverflowQueryView`. Legacy
overflow premises retain their exact sources in an operand index, including
withdrawal and branch scope. Operation-range authority checks and constant-offset
upper/lower bound helpers also consume views. Atomic variable/literal queries
keep their fixed-size native decision path; shared arithmetic is not exported.
The built difference graph's ring-overflow route also reads shared operands,
including chained bounds, modular source keys, and subtraction relationships.
General difference-graph comparison/admission adapters remain to be migrated.
Certificate premise adapters still need their across-effect availability routes
migrated before their boxed compatibility forms can be removed.

Signed and unsigned 32-bit order rules inspect operand views, including mirrored
and negative answers, shifted-bound domains, and successor transport. Their
native entry points use the same rule bodies. Fixed-size literal/variable
comparisons preserve native spelling; shared arithmetic stays in observations.
Unsigned successor, subtraction, remainder and partial-restoration guards also
read views. Low-word index comparisons retain their wide operands and literal
offsets through the unsigned or signed range checks, preserving refusals when
the ranges are absent. Nonnegative quotient/remainder bounds read retained
operands, including the signed reading of unsigned results. Their generated casts
reuse shared composition prefixes and preserve the native checking constructor;
they do not change stored terms. Signedness conversion of quotients and remainders
also reads shared operands, preserving its two sign premises, written comparison
directions and disequality polarity. Exact observation-bound provenance selects
retained sources from the existing bound index, including branch withdrawal;
it adds no index to ordinary fact admission. The common KernelTerm cast engine
keeps the distinct comparison-reading and generated-premise composition policies.
Adjacent strict/inclusive signed and unsigned word bounds also read retained
operands, including extrema, mirrored queries, and original supporting facts.
The signed equality dispatcher remains open.

Bounded arithmetic-certificate conclusion identity reads shared operands directly,
preserving its accepted operators, cast encodings, narrow comparison identity,
written directions, and payload bound. It retains the native 64-bit reflexive
constructor rule. Growing shared prefixes are checked without boxed exports;
ordinary and across-effect certificate premise adapters remain open.
Snapshot-blind candidate keys now read shared arithmetic and reuse interned child
identities across growing prefixes. Native and shared machine observations select
the same load candidates; key equality still requires the existing checked memory
bridge and is never proof authority. The load-registry lifetime invalidates the
shared key memo. The checked matcher now compares shared operand structure and
rechecks each changed load through the current frame authority. Its syntax cache
contains no proof answers or registry lookups. Certificate availability adapters
remain open.

Finite-quantifier guard ranges read signed 32-bit and unsigned 64-bit operand
views directly. They retain direction, truth, endpoint handling and signed
variable-edge propagation; arithmetic endpoints outside that rule's fragment
are refused without exporting their shared trees. The general order-fact and
certificate bridges remain separate migration work.

The shared difference-graph adapter retains range and affine-query results
across unrelated fact additions. Each cached result records the operand keys,
node bounds or edges, and child queries it read. Updates invalidate only those
readers and their parents; cloned contexts keep separate persistent caches.
Growing-prefix tests cover unresolved comparisons as well as successful range
queries. This removes a repeated-prefix walk; it does not finish comparison
normalization or remove the dispatcher's compatibility bridge.

Ordinary machine-order dispatch now retains operand views instead of exporting
observations through the general comparison bridge. Sign-bit and half-range
rules retain their written casts and narrow carrier guards. A bounded checking
form uses graph word identities and selected written constant equalities; it
keeps stored terms unchanged. Two-level cancellations inspect the queried
expression, rather than whichever application first represented a class, and
record their result so later queried prefixes reuse it. Independent operator
tests cover native/shared parity, including unknown answers and transitive
constant contexts. Growing-prefix tests cover both successful and unresolved
zero-addend and cancellation queries with unrelated fact additions.

The 32-bit equality dispatcher now reads shared operands for additive
matching/cancellation, opposite signed bounds, exclusions, direct scaled-offset
sources and refutations. The difference graph's word-equality rule also reads
views in both signedness domains, retaining non-four-byte offset consequences.
Checking reductions reuse graph word identities before interval/addend work;
growing-prefix tests cover successful and unresolved queries across changing
contexts. Source withdrawal and sibling contexts have no-export regressions.
The general comparison bridge remains for wide equality. Deeper first-use
normalization and later equality updates remain explicit audits before enabling
additional producers. Preserve rule order as well as proof results: unwrapping
a sign cast before substituting a constant can expose a different range rule,
and moving endpoint queries earlier can multiply nested bound visits.

Known-comparison lookup now retains shared operands even on a miss. The
regrouped-add domain check reads its operands and three ordinary domain premises
through views, including both choices when both children are sums. Conditional
normalization uses a cited complete domain's two ordinary bounds directly;
legacy overflow goals still require both bounds. These routes have no-export
regressions for shared arithmetic and missing-premise controls. Mixed opaque
legacy operands retain their compatibility construction and still need auditing.

Nested signed production remains disabled until checker consumers are shared
end to end. A green PR migrating a subset does **not** complete part 1.
The original pointer-read WIP branch and its historical failure list are not
the current working plan.

## Ordered migration checklist

### 1. Finish checker consumers — active

Scope: checking of arithmetic already representable by shared kernel nodes,
including successful decisions, failed decisions, certificates and premise
selection. Preserve the existing rules; a graph-only replacement that returns
unknown on formerly provable arithmetic is not completion.

Remaining groups to audit and migrate:

- [ ] Finish comparison dispatch and native premise lookup. Ordinary order
  dispatch reads views; the `native_comparison_of_integer_observation` bridge
  remains for wide equality and lookup consumers. Audit deeper first-use and
  later-equality normalization before enabling additional producers. Remove
  each remaining conversion only after its supported routes read views.
- [ ] Signed equality dispatch: additive matching/cancellation, equality from
  opposite bounds, memory/equality sources, and negative answers. Ordinary
  signed/unsigned order rules, successor transport and wide order walks already
  read views; their completion does not remove the equality dispatcher.
  Shared 32-bit arithmetic now has a view-based route, including difference-graph
  equality and source withdrawal. The native opaque/memory branches and wide
  equality remain explicit audits; additional growing additive shapes still
  need checking before enabling new producers.
  `conditions_equal_with_load_atoms` now compares shared operand pairs without
  exports, preserving the checked load-origin/snapshot callback and mixed native
  loads. Growing shared prefixes reuse syntax correspondence; authority is checked
  anew for each selected load pair. Native opaque operands retain their existing
  structural matcher.
- [ ] Atomic domain evidence and certificate premise adapters. Atomic derivation
  now reads ordinary range-domain views and retains the exact premises for
  increment, one-plus, nonnegative addition and subtraction. Their source
  lookup selects one existing order-index entry; balanced-unit sums also read
  operand views. Reassociated-add checking and conditional normalization read
  ordinary domains. Certificate availability uses the common premise store,
  including ordinary bounds supplied by a retained legacy nonoverflow source
  and its checked across-effect memory bridge. Ring-overflow decisions
  and bounded certificate conclusion identity already read views.
  `interval_query_form` remains in Surface search/output adapters and test
  references, not kernel atomic derivation.
  Atomic signed- and wide-order paths now retain the original source
  propositions. Their builders, indexed path collectors and checkers read
  endpoint views directly, preserving polarity and their existing endpoint
  connection rules without exporting shared arithmetic. The signed collector
  retains constant connections and selected memory bridging. Range-membership
  and memory-frame path consumers now retain those original sources too; boxed
  path adapters remain only as test references. Individual signed-order domain
  steps also retain shared endpoints and exact source propositions; legacy
  inputs retain their written forms for existing canonical memory comparisons.
  Their source selection and checks no longer export shared arithmetic.
  Symbolic conjunction-cycle checks also use retained endpoint identities,
  preserving strictness, mirrored polarity and the separate finite-range rule
  for cycles through constants. Canonical range-bound lookup and
  nonnegative induction-domain admission read indexed endpoint views directly;
  the native bound-entry exporter remains for the other evidence and output
  callers.
  Singleton constant evidence now retains the original bound propositions and
  their selected constant equalities, reading endpoints directly from views.
  Range-bound path evidence, including its strict-successor route, also retains
  source propositions and checks each edge and constant connection without
  exporting arithmetic. Growing-prefix admission uses an indexed execution-id
  ceiling lookup; named loads still resolve their live snapshot dependencies.
  The graph-only derived-order query and order-shape
  classification read views. Difference-graph order admission now retains shared
  operands and reads the existing domain/operand-key index without exporting
  arithmetic, including deferred cast, sign-flip and affine links. Native
  queries retain their compatibility index until those consumers migrate;
  repeated native queries must not re-import their complete expression trees.
  The graph's 32/64-bit equality and exclusion admission now reads operand views;
  its 64-bit residue index retains shared keys and preserves the existing depth
  and edge limits. Fresh equality aliases reuse the existing coordinate instead
  of growing a chain of equivalent nodes. Native admission following a shared
  bound must reuse that coordinate too, preserving its earlier constraints.
  Wide graph equality queries read views, with the existing native-only lookup
  path retained for already-written inputs. Native residue keys are recorded
  during admission so unrelated query contexts do not pay cold import work.
  Native imports reuse the opposite signedness observation's DAG when available,
  changing only the root's numeric interpretation. Explicit native constructors
  retain a later supplied boxed input; query-only imports leave shared storage
  untouched. Shared narrow graph admission and queries use the existing
  value-preserving 32-bit widening, passing the widened view directly rather
  than rebuilding a condition whose reader can recover the narrow form.
  Fresh narrow aliases share their original-domain coordinate before widening;
  equivalent cast nodes must not grow until they exhaust the bounded graph
  walk. The higher-level wide dispatcher still needs migration; these graph
  changes do not complete that consumer.
  The masked-zero equality rule now reads retained 64-bit operands and keeps
  its bound as cited evidence. Native and shared inputs use the same rule;
  absent or refuted bounds remain unknown. Recorded wide-equation endpoint
  queries also accept shared operands, retaining logical-read dependencies,
  current equality classes and the original source endpoints. Pointer-address/tag
  forms and fact-dependent wide simplification still need migration before
  removing the wide-equality compatibility bridge. Wide arithmetic and bitwise
  syntax now have an iterative, session-memoized checking reading over shared
  nodes. It preserves the existing native constructor rules, including unsigned
  subtraction's atomic-only identity and signed/unsigned observation types.
  Casts and opaque nodes remain boundaries; this reading consults no facts and
  never changes the written term. Native/shared constructor parity and growing
  shared prefixes cover this part of the simplifier. The dispatcher still needs
  the tagged-address route: disabling its bridge loses both `x & ~3 == x` and
  `(x | 3) & ~3 == x` when `x == address(p)` and `p` is aligned.
  Shared scalar dependency admission now stores syntax edges and attaches facts
  at their roots, instead of filing every prefix under every variable. Each
  node propagates at most two distinct witnesses along a monotone branch;
  singleton and existence queries read those witnesses. Complete selection
  follows the reverse edges once and preserves source ordering. Native and
  registered-load dependencies retain their existing indexing. The original
  distinct-variable growing-prefix regression now passes without exports;
  candidate parity, branch isolation and withdrawal are checked separately.
  Integer certificate native premise availability now uses ordinary shared
  lookup, including mirrored native sources across a checked memory frame.
  Both certificate-local boxed retries are removed. Nonoverflow source lookup
  reads shared operands and selects the existing snapshot-blind source bucket;
  matching still requires the checked load authority. That common authority also
  recognizes an explicitly held equality between named word loads before
  discarding their names in favor of raw origins.
  The common arithmetic-comparison rewrite now reconstructs the shared machine
  fragment directly, with memoized syntax work and the existing checking-only
  simplifications. Scope-dependent rewrites keep local memos. A registered-read
  rewrite exposing an Integer-to-machine conversion now retains that
  existing typed conversion node inside the shared machine DAG when
  its payload has a structural identity, retaining its scoped Integer payload
  and ordinary stored-value reasoning. Payloads containing producer-local
  legacy identities remain outside this fragment.
  The original reproduction expanded five DAG nodes into 31 boxed nodes; the
  shared conversion path avoids those exports.
  Keeping only the canonical read name was tried and rejected: it lost premise
  matching between a read of stored `7` at `p[i + 0]` and the corresponding
  claim about `7`. Preserve that positive matching control alongside no-export
  and growing-prefix checks. Other opaque read values and explicit native
  rewrites remain compatibility boundaries to audit; they must not silently
  export surrounding shared arithmetic before part 1 is declared complete.
  Memory-order checking now reads endpoint views, retaining its
  equality simplification, extreme bounds, successor rules and unsigned-domain
  guards. Native/shared decision parity and changing-context growing prefixes
  have no-export coverage. Its changing-context test also caught the cached
  difference graph ignoring shared order additions and withdrawals: the source
  filter now recognizes the same order views as graph admission. Explicit native
  arithmetic queries reuse a retained import to read the shared graph coordinate;
  native-only graphs keep their existing lookup path. Opposite unsigned bounds
  now prove equality through either representation, while either bound alone
  leaves equality unknown. Sibling-branch
  admission also exposed repeated syntax installation for growing expressions
  with only one or two variables. Those bounded dependency sets now attach
  directly to variable nodes; larger sets retain adjacency indexing. Equality
  registration also uses the cached syntax summary to skip pointer discovery
  for plain arithmetic without load names, retaining scoped inspection for
  conversion payloads and load-bearing expressions.
  Selected-condition paths and their quantified/derived order collectors
  retain operand identities. Their transport equality reads shared operands,
  retaining the existing native leaf rules, logical-load registration, scoped
  memoization, positive-offset connections and constant connections. Guarded
  derived bounds remain unavailable without the guard; finite universal
  instances retain their substituted operands. Variable substitution now rewrites
  shared machine observations directly, preserving raw arithmetic operators and
  existing cast rules. Substitution results remain query-local, including when
  registered-load resolution is enabled. Additive matching counts shared
  DAG occurrences with exact multiplicities rather than flattening every path
  into a list; constant accumulation retains its existing wrapping semantics.
  `condition_as_order_fact` occurrences in `order_paths.rs` and the
  proposition-reasoning regression are test-only reference walkers.
  Memory-equality candidate construction now reads retained bound operands
  and registers their indexed addresses directly in the equality graph.
  Internal affine address normalization also registers retained atoms directly,
  without exporting them for sorting or reconstruction. Query registration
  preserves current block aliases and adds no storage or permission evidence;
  the existing coverage check still validates the selected supplier.
  `signed_order_bound_entries` remains a Surface planning adapter; its
  proof/facts occurrence is test-only. Kernel uses of `interval_query_form`
  are also test references; its live callers are Surface planning/output
  adapters.
- [ ] Remaining difference-graph comparison/admission and interval-query
  adapters. Wide constant evaluation and the wide interval entry points already
  read views; preserve width and source evidence in the remaining consumers.
- [ ] Remaining conversion, inverse-operation, modular and
  condition-identity adapters, including observation lookup forms. Distinguish
  live checker consumers from test-only reference exports and explicit legacy
  producer/output boundaries.
  `TermRewrite::integer_shared` retains unguarded machine observations across
  exact Integer congruence, compound machine-source replacement and typed
  variable substitution. Exact congruence preserves raw operators and casts;
  selected source/replacement imports are cached per numeric interpretation.
  Conditional narrowing and remainder reductions now retain shared operands
  and consult only their selected guards. Native order premises reuse the
  existing retained-bound index, including promoted narrow readings; structural
  matches retain the original cast premise before checking reads through it.
  This lookup stays within the selected rewrite context: indexing native orders
  in the general observation lookup changed unrelated automatic search and
  exhausted the false-loop-invariant fixture's budget. Unrelated equality and
  literal queries keep their existing fast paths. Equivalent 32-bit literal
  spellings share an operand key while retaining their original source facts. A cached syntax
  summary lets conditional queries skip unchanged arithmetic prefixes.
  Tests cover native/shared parity, omitted and refuted guards, full-width
  bounds, source withdrawal and changing-context scaling without exports.
  Structural pointer-tag bounds now read operand views and memoize shared DAG
  nodes, including misses. Guarded tag bounds read exact retained order edges
  and retain their original sources; signed carriers still require both a
  nonnegative lower bound and a small upper bound. This migrates the bound
  consumers, not the surrounding tagged-address form or wide equality dispatch.
  A machine observation converted back to its exact original format now joins
  the original word in the equality graph, retaining both written application
  nodes. The rule handles retained shared operands and existing opaque values
  without exporting surrounding arithmetic. Different widths or signednesses
  still need their ordinary range evidence. This closes the missing inverse
  identity inside larger arithmetic; it does not migrate opaque term storage.
  The scoped term rewriter retains machine fold endpoints during carrier
  collection and substitution, including capture-avoiding binder renaming.
  Fold congruence also interns retained endpoints directly at the range's
  machine width. Shared endpoint DAGs no longer export for these traversals.
  The separate
  exact-equality rewrite adapter still needs its own parity audit; its native
  canonical-load and pointer-address matching rules must be preserved.
  The carrier collectors also retain shared machine observations and fold
  endpoints for Integer variables, binders and scope reservations. Conversion
  payloads and registered loads use the original collector-specific callbacks.
  Maximum-name queries read the syntax index's greatest member and selected
  load names, rather than enumerating every variable of each growing prefix.
  Mathematical variables inside a machine endpoint's conversion payload are
  included even when the C item binder has the same numeric identity.
  Opaque leaves outside the shared operand fragment still require a
  parity/no-export audit of the compatibility bridge.
  `reasoning/path_facts.rs::decide_with_facts` retains comparison readings and
  matches direct path facts by shared comparison identity. Its 32-bit guards
  have no-export coverage; unresolved 64-bit guards still reach the general
  wide-equality exporter through intrinsic checking.
  Signed 128-bit division guard lookup now uses shared proposition keys for
  both native and observed compound premises. The boxed `read_observation_form`
  adapter is removed; structural `canonical_observation_form` remains an
  explicit producer boundary. `native_reading_of_integer_observation_fact`
  remains a Surface planning/output adapter.
- [ ] Remove redundant checker exports and enforce the boundary with tests.

**Completion criteria:**

1. No live checker route exports a shared arithmetic operand to a boxed tree to
   inspect it or decide a premise. Explicit Surface output belongs to part 4.
2. Native and shared inputs preserve positive proofs, negative answers,
   unknown answers, domain requirements, source evidence and branch isolation.
3. End-to-end regressions cover `x < x + 1` with and without its domain,
   arithmetic pinned by equalities, unresolved bound comparisons, casts,
   signedness/width changes and ordinary arithmetic domain obligations.
   Both successful and unsuccessful queries leave shared operands unexported.
4. Deterministic scaling covers growing DAG prefixes, changing proof contexts,
   and unrelated facts. A fixed-context recursive cache alone is insufficient.
5. `scripts/check.sh` passes, including expansion/rechecking and all ordinary
   scaling tests. No raised limits, weakened proofs or nightly run substitutes.

**Compiler-guided accessor inventory (2026-11-05, `136f64774` tree):** a
throwaway build marked `SharedMachineIntegerTerm::value`,
`SharedIntegerRangeEndpoint::value`, and the forwarding `MachineAtom::value`
deprecated, then ran `cargo check --lib --features fast-gate
--message-format=json`. It identified 74 distinct source-line sites (down from
107 at `863cc08da`). These include guarded legacy reads, native reconstruction
and explicit output adapters; the count is not a count of defects. Classify each
route against the completion criteria above. The temporary annotations are not
part of the implementation. Checked rewritten-load evidence in `proof/facts.rs` now caches structural
correspondence for pairs of shared observations. It selects differing leaves
without exporting their surrounding arithmetic, then checks current load
registry/snapshot/premise authority. Cached syntax is never authority; differing
compound roots under binders keep their existing refusal. Cold doubled DAGs
and growing prefixes at 16/64/256 retain shared terms, including branch and
registry-clear refusal controls. Mixed shared/native observations and native
evidence construction for a selected load-versus-compound replacement remain
explicit boundaries to migrate; this does not complete the memory comparison
audit.

Exact equality substitution now retains shared arithmetic in machine observations
and machine range-fold endpoints. Reconstruction preserves the native rewrite
constructors, including raw 32-bit sums/differences, legacy cast encodings and
literal spelling. Pure arithmetic rewrites reuse syntax results; load-bearing
rewrites retain query-local registry-dependent results. Differential tests cover
widths, operators, casts and load canonical matching; cold DAGs and growing
prefixes cover both observations and fold endpoints without boxed exports.
Opaque replacements that leave the shared producer fragment still reach the
native reconstruction boundary and must be migrated before part 1 is complete.

Scoped machine rewriting now accepts shared source operands as well as shared
replacements. Native output carriers compare the selected source syntax through
operand views; shared observations match retained nodes without exporting the
source. Variable shadowing, capture avoidance and composite-source binder
refusals retain the native rules. Shared replacement capture summaries are
collected when a binder or fresh name needs them, avoiding repeated variable
enumeration for growing replacements in ordinary rewrites. Differential tests
cover source syntax and binder behavior; growing source DAGs and replacements
with distinct variables have no-export scaling regressions. This provides the
source interface needed by the pending modular projection migration; it does
not remove that projection's native output boundary yet.

Scalar reads now have an owned `KernelTermNode::MemoryLoad` descriptor: shared
memory version, address and read kind. Generic import retains that structure
instead of a producer-local opaque load. Generic imports and arithmetic storage
now adopt a registered scalar read's descriptor together; changing only one lost
matching across these paths. The transitional registered-read bridge caches the
descriptor per format, so repeated conversion does not walk the address again;
the retained term survives registry clearing and cache state travels with registry
capture/restore. Native export and existing typed Surface read spelling preserve
the descriptor. Stored values, observation origins and access permissions are not
part of its identity. The process-wide interner keys a read's snapshot by arena
identity, avoiding structural memory comparisons between verification sessions.

This is a representation foundation, not completion of part 1. Read addresses
still use native `Pointer` payloads; addresses outside the exact structural
fragment keep their existing legacy representation. Checker observations admit
structural reads in machine arithmetic; reads nested inside mathematical conversion
payloads remain outside that fragment. The subsequent scalar producer and
metadata cutover is described below. It preserves structural read-version
selection and keeps separation-dependent frame equalities in proofs. Pointer-valued and
volatile reads need their own representation audit. Scaling regressions cover
retained arithmetic prefixes beside unrelated memory and repeated imports of a
read with a growing address; explicit native import still pays for its input.

The lexical read/address collectors now have a borrowed read-node route.
Variable collection, Integer-carrier collection, capture/scope summaries and
rewrite carrier collection select shared reads from a persistent syntax summary
and inspect their addresses directly, without exporting surrounding arithmetic
or looking up a reserved variable. Read-free arithmetic skips this traversal.
The summary preserves each collector's existing snapshot and binder policy;
it is syntax, not evidence of access or availability. A doubled-DAG regression
checks growing read selection without repeated prefix expansion.

Current-memory collection also reads shared descriptors with a retained width
context: generic casts reset the inherited width, while other operators retain
the existing native carrier rule. Its syntax summary caches no snapshot-match
or permission answers. Native/shared tests cover formats, casts, absent widths
and changed snapshots.

Shared checker observations now retain read descriptors. Selected equality
matching, comparison rewriting and graph registration accept them without
exporting surrounding arithmetic. Address rewriting preserves the selected
snapshot rather than repeating creation-time version selection. The graph reads
width and epoch-scoped origin metadata through a selected-read interface; changing
the observation format neither widens the access nor renews its origin. Metadata
now belongs to a read-descriptor observation index: snapshot, address and read
kind select width and epoch-scoped origin independently of any reserved name.
Capture/restore shares its persistent roots with the verification session. The
central comparison-form collector also selects structural reads inside Integer
observations, preserving
read-over-write matching without adding individual-check fallbacks.

PR #2480 merged the independent metadata increment. Its full local gate passed
7,610 unit/API tests, 58 regular examples and 5,079 Markdown fixtures. The run
took 17m54s including compilation and emitted the ten-minute warning; budgets
were not raised and the nightly suite was not run.

The ordinary integer producer switch is in progress on
`codex/structural-scalar-producers`; it has not been published or merged.
The integrated cutover passed the unit/API phase (7604 tests) before the latest
consumer repairs, but the full gate is not green. The focused fixture recheck
currently passes 39 of the original 42 failing Markdown fixtures; three example
projects still fail. `input-cursor` now passes unchanged: ordinary integer read
facts no longer enter the legacy load-time transport index, avoiding repeated
history walks during resource expansion. A deterministic regression covers
16/32/64 read facts without growing transport work. Re-run the full gate,
selected expansion checks and fact-stability audit after completing these repairs.

The decrement fixture now passes unchanged. Certificate spelling recognizes exact
structural read atoms (snapshot, address and kind), and observation casts retain
nested historical Surface operands. `label-build-flags` also passes: dynamic
resource dependencies validate the original loan binding after proving coverage,
rather than inventing a narrower binding that loses its coverage premises.
Wrong-holder, ended-loan and missing-range controls remain rejected.

The remaining original Markdown failures are the two loop-exit disjunctions and
`uninitialized_destination_beside_a_viewed_source`. The latter has a passing
explicit proof; its automatic range split now recognizes shared comparisons and
proves the earlier-index arm, but still misses the boundary arm. The loop-exit
cases await the user decision about ordinary obligation discharge before the
existing exact `cases` split. Do not change that rule implicitly.

The remaining examples are `arena`, `owned-vector`, and `sequence-transform`.
An explicit transport proves the untouched `arena_init` field across its loop;
the expanded trace then reaches a later quantified guard comparison in
`arena_alloc`. Explicit element equalities at function exit prove the unchanged
sequence contract. Investigate child-goal spelling after its conjunction split:
the written sequence equality represents the whole conjunction, while generated
children can lose their Surface forms. These diagnostic proofs are not shipped
as fixture workarounds; the producer cutover remains unready for publication.

The ordinary integer producer switch follows the address-index migration.
Execution, contracts and resource cells retain structural reads for signed and
unsigned 8/16/32/64/128-bit values. They no longer mint scalar names or emit
scalar defining equations. Read observations retain widths, historical origins
and branch-local metadata independently. Creation-time version selection remains
structural; stored literals and reads of other addresses do not replace the
selected read. Checking may still establish their equality.

The ordinary scalar bridge is removed from graph read registration, comparison
rewriting, exact-cell derived reads, origin evidence and historical synthesis.
The reserved-name machinery remains for pointer-valued/volatile producers and
compatibility with their existing facts; this increment does not migrate those
families. Arithmetic certificates accept structural read atoms with exact
snapshot/address/kind identity, and binder checks inspect the selected read's
address rather than mistaking it for an unscoped variable. Array runs preserve
read atoms without expanding their stored snapshots.

PR #2472 merged the address-admission prerequisite: structural reads inside a
scalar read's native address retain their snapshots and read kinds. Its
separate nested-snapshot key was needed while indices still held native trees.

PR #2477 switched C/Click address indices to shared machine operands. The common producer imports registered read names into structural
reads; scaled offsets retain those shared children. Their identities include
nested snapshots, replacing the separate snapshot-key walk. Canonicalization
retains each constructed child rather than resolving its read or reopening its
prefix. Opaque legacy indices retain their complete producer-local payloads and
remain outside shared scalar-read admission. That increment left scalar producers
outside this boundary and width/origin metadata on the registry; the subsequent scalar switch described above removes
that dependency for ordinary integer reads.

The producer cutover also exposed three compatibility gaps. Exact rewrite
matching now recognizes a registered name and its structural descriptor before
stored-value folding can make their native canonical forms differ. Fold endpoint
reflexivity compares shared index identities. The difference graph indexes a
named read's structural descriptor at admission, so range queries reuse its
recorded bounds without a query-specific fallback. The owned-string example,
historical fold endpoint, and preserved-call range fixture pass unchanged.

Validation: `scripts/check.sh` passed 7,597 unit/API tests, all 58 regular example
projects, and all 5,065 regular Markdown fixtures. The local run took 12m53s and
emitted the ten-minute budget warning; deterministic scaling tests passed without
relaxing work budgets. Another 147 focused tests and selected nested-index and
uint64 resource-fold positive/negative fixtures passed. New controls cover cached
registered names, registry clearing, annotation payloads, stored values,
cross-arena snapshots, named/structural bound lookup in either admission order,
and nested producer chains beside unrelated memory with warm and cleared caches.
The focused `nested_index_read` fact-stability audit reports zero differences
before and after the change. Its spelling census records 36 spellings and zero
misses. Both audit harnesses passed; the nightly suite was not run.


The checker-admission increment merged in PR #2468. Its initial full gate passed 7,551
unit/API tests but exposed nine fixture failures. Named-read replacement inside
shared Integer observations repairs bounded-pool, owned-string and
`definedness_before_a_rewritten_sum_claim`; retaining read identity in arithmetic
certificate matching repairs `integer_cast_identity_unsigned_subword_promotion`.
Arena now also passes unchanged: resource containment/separation comparison keys
use shared scalar identities for numeric arguments, retaining the original source
and complete nonnumeric/pointer metadata. Its rejected allocation size contained
a structural read where the held fact contained the same read's registered name.
Multifile-registry now passes after selecting the read snapshot before a
qualified address spelling; owned-vector passes after read comparison descends
through logical connectives. The false-model-invariant fixture again reports
the intended rejection: connected equality search leaves implication/forall
wrappers to the existing introduction/body route. The remaining original fixture
failure was `a_self_aliased_field_operand_is_one_value`; it now passes unchanged
after the goal/obligation spelling repairs below. Do not switch producers or
remove the registry on the strength of focused-only success. Keep the original programs, proofs and budgets in these checks.

Read comparison now batches selected replacements in one proposition traversal,
with capture avoidance and opaque snapshots/sealed resource bodies. The scaling
control grows the number of reads inside one proposition, rather than testing
many single-read propositions. Read graph inputs preserve exact registered
snapshot/width identity, and typed symbolic cell runs record their value width
before producing reads. Selected read authority also reaches shared equality,
transport, order-index/walk, and pointer-tag consumers. Aligned sums reuse the
cached structural leaf correspondence before graph signatures; arbitrary
memory-dependent permutations remain an audit item.

The remaining addition failure was traced to goal spelling: the stored sum's
candidate had the correct shape, but strict premise lowering rejected its
unproved overflow obligation before the proof driver could solve it. Proposed
`have` goals now use private obligation collection only for spelling identity;
the ordinary driver still proves their prerequisites. Existing premise citations
remain strict, including inside an outer obligation probe. Fixed-state and
focused-outcome obligation spelling now receives the proof's indexed recorded
snapshots, so an intermediate read can be named while proving the stored sum's
domain. The original alias fixture and three focused obligation controls pass.
The fresh `scripts/check.sh --no-fail-fast` gate passes: 7,584 unit/API tests,
58 examples, and all 5,057 mdtests. It took 15m06s including compilation
on this environment, exceeding the ten-minute target; no limits or gate selections
were changed. PR #2468 merged this checker increment;
read producers and reserved-variable removal were deferred to the subsequent
increments described above.

The batch comparison form retains literal machine truth/falsehood after replacing
reads, while ordinary rewriting keeps raw comparison syntax. Comparison keys now
use an iterative connective traversal and boxed resource payloads, preserving the
supported depth boundary and linear selected-node work. The disjunction expansion
regression checks the complete printed certificate with implicit search disabled;
shared read matching lets the existing checked `extract` rule project its held
disjunction without an additional `cases` proof.

| Remaining audit group | Main consumers |
| --- | --- |
| Wide equality, tagged addresses and mixed opaque operands | comparison dispatch, pointer-tag forms, shared rewrite compatibility, arithmetic reconstruction |
| Fold checking and equality | opaque outputs from exact equality rewriting; native-output reconstruction boundaries |
| Dependency and selected-atom walkers | native-carrier reconstruction boundaries; verify remaining guarded legacy reads |
| Numeric checking helpers | modular reconstruction, operation mappings and signed-arithmetic adapters |
| Explicit compatibility output | Surface bound/planning adapters, diagnostics and affine-offset spelling; check their callers before treating a path as output |
| Guarded legacy branches | imports, cast readers, graph interning and collector branches that already retain shared inputs |

Signed-certificate atom identities now use retained KernelTerm keys rather than
flat token vectors. Native input parsing and shared operand views produce the
same keys, preserving casts, low-word observations, operator widths and opaque
atom classification. The mathematical-result adapter retains shared operands
through checking-only cast canonicalization; narrow observations keep their
explicit widening and unsigned 32-bit observations remain outside the signed
fragment. Integer conversion payloads remain refused by this certificate grammar,
as on the native path. Shared prefixes and map-key operations reuse syntax;
no lowered value or proof authority comes from these keys.

The intrinsic format-range check now reads the outer cast through an operand
view. Its bound decisions retain true, false and unknown answers without
exporting the observed arithmetic, including growing prefixes and narrow
widenings.

Caller classification: `resource_tracker::collect_integer_node_reads` feeds
`reads_of_proposition` and the version-mismatch diagnostic helpers, not proof
admission; its export belongs to the output audit in part 4. The public
`IntegerTerm::max_variable` compatibility helper has no in-repository callers.
Neither is evidence of a remaining live checker export.
`resource_steps::observes_machine_arithmetic` is used only by the missing-fold-
guard diagnostic, so it belongs to part 4 too. `uint32_order_bound_entries`,
like its signed counterpart, is called only by Surface proof planning. In
contrast, `recorded_less_equal_candidates` feeds
`exact_less_equal_for_memory_resolution`: its retained endpoint exports remain
a live checking dependency. Preserve its written-premise checks and memory
identity evidence when migrating it; its existing candidate-bucket enumeration
must not acquire an additional scan.

Current-snapshot memory-load collection retains shared observations and fold
endpoints. It visits cached conversion syntax, then applies the existing
memory/width/opaque-carrier rules to the retained Integer payloads. Snapshot
answers are recomputed per query; syntax caches contain no memory facts. Fold
alpha identities also retain machine endpoints and recognize conversions nested
inside shared arithmetic, retaining endpoint outer scopes and index widths. Constant
endpoint emptiness checks inspect operand views. The conservative accumulator
carrier check decides composite roots directly instead of collecting their
variables before returning the same conservative answer.

Fold endpoint equality now uses retained operands and selected exact equality
sources. Native equality pairs are indexed when admitted, separately from
general observation lookup; the existing native-query work boundary remains
unchanged. Signed endpoint matching counts DAG occurrences with the original
separate positive/negative multisets. Multiplicities and constants wrap in the
32-bit word ring, avoiding growing big-integer work on cold doubled DAGs. Syntax-only memos
reuse constant spines and previously checked Add/Sub child equalities across
proof contexts; exact fact-derived answers never enter those memos. Operand
keys reuse the session's admitted arithmetic imports, avoiding a second tree
walk when a native equality enters the selected-pair index.


Fold item-range guards now use the common retained comparison constructor.
Fold-bound dependency collection preserves endpoint outer scopes, initial-value
variables and conversion payloads without expanding shared arithmetic. Checked
fold-step substitution accepts a retained replacement operand; shared machine
observations and nested binders keep that operand through capture-avoiding
rewriting. Native output carriers still require a written machine term, and
that output conversion remains explicit at reconstruction rather than occurring
unconditionally before substitution. Its mixed-carrier callers remain part of
the compatibility audit.

Fold empty/append laws and predecessor construction now retain machine
endpoints, including the checked increment bound and item observations. Their
checking-only ±1 reconstruction shares the arithmetic-comparison memo and
preserves the existing native constructor readings. Exact premise matching
recognizes a retained order observation and a native comparison of the same typed
operands, without exporting arithmetic or consulting proof facts; wrong bounds
and opposite polarity remain unavailable. The existing explicit `peel ... using`
regression covers the full-width unsigned bound. Both endpoint widths have
cold growing-DAG no-export coverage.

Selected equality-atom collection now reads retained machine observations.
Syntax-only persistent summaries retain written variables and 32-bit constants;
wide literals and Integer conversion payloads keep the native collector's opaque
rules. Load-address atoms are resolved against the current registry after the
syntax-cache borrow ends. Growing prefixes and cold doubled DAGs reuse shared
summaries without exports; clearing the registry cannot preserve old address
atoms. Existing indexed candidate-bucket enumeration is unchanged by this
representation migration and retains its separate search/scaling audit.

### 2. Finish expression producers — after part 1

- [ ] Enable nested signed arithmetic construction, collecting the existing
  scoped obligations in evaluation order without proving them during lowering.
- [ ] Migrate remaining deferred/partial operations and C execution producers.
- [ ] Check actual obligation discharge and failure, including C and Rust shift
  differences, division/remainder, quantifiers and short-circuit conditions.

**Done when:** these producers construct shared nodes directly; no repeated
prefix export occurs during execution or checking; undefined cases remain
refused. Keep the `forward_conversion_requires_symbolic_argument_definedness`
negative regression: claim completion must not bypass evaluation obligations.

### 3. Finish term families

- [ ] Replace opaque legacy payloads for algebraic values, binders, loads and
  full pointer values with common typed nodes and common fact/goal operands.
- [ ] Preserve pointer provenance, bounds, qualifiers and historical identities.
  The proposed CPointer field design is unresolved; this migration does not
  authorize changing pointer semantics or declare issue #2179 resolved.

**Done when:** each migrated family has structural construction and exact
raising/lowering tests, and its legacy payload/adapter has been removed.

### 4. Finish common lowering/raising and remove obsolete representations

- [ ] Raise common nodes directly, including machine terms currently exported
  once to the old speller.
- [ ] Remove obsolete imports, exports, aliases and parallel term trees as
  their last consumers disappear. Retain frontend evaluation structures only
  where they represent genuinely different source/evaluation information.

**Done when:** the common path handles facts and goals without compatibility
representations, spelling searches or placeholder fallbacks.

### 5. Audit and enforce spellability

- [ ] Run fresh fact-stability and written/smart spellability censuses. Historical
  counts are not a current inventory; reduce each remaining miss before fixing it.
  The `design/charon-trial/held-values` census still has `unfold` equations
  with a `match` right side and a call precondition instance recorded before
  its result. Preserve `charon_held_value_locals_are_spelled_by_name` coverage.
- [ ] Name any remaining introduced values/states and supply missing fact syntax.
- [ ] Enforce `lower(raise(x)) == x` for every fact added by a checked step and
  every focused goal, with a census ratchet preventing regressions.
- [ ] Retain near-linear stepping and shared-DAG scaling regressions.

**Done when:** the fact-stability audit has zero differences, the written-step
census has zero misses, the common round-trip checks hold, and the gate passes.

## Delivery and history

Land coherent tested slices in small PRs, one open PR per thread. Enable
merge-when-ready after publishing; inspect queue state before updating a head.
Do not mark a checklist group complete merely because its latest slice passed.
Ask the user for semantic decisions, not routine implementation order.

The detailed chronological handoff, old branches, trials, dropped approaches
and validation logs remain in the
[pre-consolidation history](https://github.com/clicklang/click/blob/1e4e07c98fb5354cf6a14ce985c08d5af95f286c/roadmap/unspellable-facts.md).
Use that for historical evidence, not as a current outstanding-work list.
