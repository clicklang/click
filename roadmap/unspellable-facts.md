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
shared key memo. Migrating the checked matcher and certificate availability is
still necessary before removing their native comparison adapters.

Finite-quantifier guard ranges read signed 32-bit and unsigned 64-bit operand
views directly. They retain direction, truth, endpoint handling and signed
variable-edge propagation; arithmetic endpoints outside that rule's fragment
are refused without exporting their shared trees. The general order-fact and
certificate bridges remain separate migration work.

The general comparison dispatcher still needs its compatibility bridge. Its
migration must preserve the existing rule order as well as proof results;
moving endpoint queries ahead of cheaper rules can multiply nested bound visits.

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

- [ ] General comparison dispatch and native premise lookup. Remove the
  unconditional `native_comparison_of_integer_observation` conversion in
  `condition_reasoning/decision.rs` and lookup callers only after all of their
  supported proof routes consume operand views.
- [ ] Signed equality dispatch: additive matching/cancellation, equality from
  opposite bounds, memory/equality sources, and negative answers. Ordinary
  signed/unsigned order rules, successor transport and wide order walks already
  read views; their completion does not remove the equality dispatcher.
- [ ] Atomic domain evidence and certificate premise adapters. Migrate the
  remaining `interval_query_form` callers in atomic derivation, reassociated-add
  checking and conditional normalization. Certificate availability must retain
  its checked across-effect memory bridge. Ring-overflow decisions and bounded
  certificate conclusion identity already read views.
- [ ] Remaining difference-graph comparison/admission and interval-query
  adapters. Wide constant evaluation and the wide interval entry points already
  read views; preserve width and source evidence in the remaining consumers.
- [ ] Remaining sign-bit/conversion, inverse-operation, modular and
  condition-identity adapters, including memory-order checking and observation
  lookup forms. Distinguish live checker consumers from test-only reference
  exports and explicit legacy producer/output boundaries.
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
