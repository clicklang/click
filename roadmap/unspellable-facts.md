# KernelTerm / SurfaceTerm: finish the representation split

Priority: P1.

Soundness: incomplete. No false acceptance is known from a missing spelling.
A missing spelling can lose proof completeness or prevent checked expansion.
Removing a compatibility checker without preserving its rules also loses
completeness and is not a valid migration.

## Goal and invariants

**Current priority: finish the KernelTerm / SurfaceTerm split.** This milestone
has a finite representation and consumer checklist. Eliminating every existing
spellability defect is a separate follow-up, not its completion criterion.

`SurfaceTerm` represents source expressions. `KernelTerm` is the common typed,
immutable expression DAG used by kernel expression producers and consumers.
Lowering can make implicit conversions explicit: two Surface expressions may
lower to the same kernel term. Raising a supported common term must preserve its
identity: `lower(raise(x)) == x`. The reverse direction preserves a canonical
spelling, not every detail of the original source text.

The broader requirement that every proof-state fact and goal has an exact
spelling remains in [Spellability](../docs/internals/spellability.md). Closing
this migration does not declare that broader project complete.

Preserve these rules throughout the migration:

- Lowering is structural and fact-stable. Facts may discharge obligations or
  establish equalities; they must not choose or simplify the constructed term.
  Equalities belong in the equality graph or comparison form.
- Definedness remains separately scoped ordinary propositions, discharged by
  ordinary proof checking. Preserve the current C/Rust and specification
  semantics; this migration does not redesign them or restore guards in values.
- Preserve positive proofs, refusals, unknown answers, source evidence and
  branch isolation. Replacing a compatibility rule by an unknown answer is not
  migration completion.
- Work stays near linear up to indexing factors. Do not export a growing DAG to
  a boxed tree at every prefix, repeatedly index all its variables, or scan
  ambient facts/history to recover a representation.
- Values and effect points retain their introducing names: call `.result`,
  heap `.allocation`, recorded states and volatile `.read_event(i).result`.
  Internal handles are permitted; they are not public spellings.

## Current position

Baseline for this revision: `93c5fe74c`, including merged PR #2492.

Already landed:

- Common `KernelTerm` nodes and `SurfaceTerm`; `ContractExpression` is an alias
  of `SurfaceTerm`, not a separate expression tree.
- Shared machine arithmetic, casts and many comparison, interval, certificate,
  rewrite and dependency consumers. Ordinary definedness obligations are
  separate from lowered terms.
- Structural ordinary integer, object-pointer and function-pointer reads,
  including historical read identities and shared address-index operands.
- Volatile observation result names (#2492), with typed value retention and
  branch/indexing controls. Specification reads no longer emit C access events.

**The split is not complete.** Source inspection still finds a live wide
comparison export, a restricted signed producer and generic legacy payloads.
These are concrete migration boundaries,
not a count of every remaining defect in the verifier.

The previous document interleaved open boxes with later paragraphs completing
parts of them. Its old unchecked lists and historical accessor counts must not
be treated as a current to-do list. The detailed evidence is preserved in
[the pre-revision roadmap](https://github.com/clicklang/click/blob/93c5fe74cd6ff161782b65a9709ffe57cd3eca76/roadmap/unspellable-facts.md).

## Ordered closure checklist

### 1. Close the remaining checker boundaries — next

Finish the checker consumers before enabling the remaining shared producers.
The bounded caller audit below is complete as of 2026-11-09, at upstream
`fe8c6d931` (PR #2500). Step 1 is **not closed**: seven route groups still have
checker exports. Close these concrete routes before enabling more producers.
A textual accessor occurrence alone is not evidence of a checker dependency.

| Route/group | Evidence and required closure |
| --- | --- |
| Wide comparison dispatch — closed | `decision.rs` sends retained operands to tagged-address reasoning. Residual tag arithmetic stays shared, exact source premises and selected native read transport are preserved, and the dispatcher no longer exports shared operands. Fixed-size atoms and already-native comparisons retain their native rules. |
| Memory-resolution bounds — closed | `recorded_less_equal_candidates` retains operand views and the order index retains original true signed `<`/`<=` source membership. Memory equality reads shared arithmetic and selected native read leaves without exporting endpoints; parity, withdrawal, direction and DAG scaling controls cover this boundary. |
| Mixed operands and reconstruction — open | R1–R6 below identify live callers and reproductions; successful all-shared cases do not close their mixed/opaque fallback paths. |
| Dependency and atom walkers — partly closed | Ordinary scalar carriers, selected atoms and shared memory dependencies retain their operands. Shared pointer-index payloads still reach native walkers through implicit `Deref`: R7. |
| Output and dead helpers — classified | See the separate boundary inventory below. Native output construction, diagnostics and test references do not establish that a checker inspected a shared tree. |

- [x] Close the memory-resolution endpoint export.
- [x] Close the wide-comparison export after migrating its tagged-address consumer.
- [x] Classify the remaining audit groups and record legitimate native/output boundaries.
- [ ] Close R1–R7 with parity, refusal, no-export and deterministic scaling regressions.
- [ ] Remove the obsolete checker adapters and retain no-export regressions.

**Done when:** no checker exports a shared expression to a boxed tree to inspect
it or decide a premise; native/shared rule parity, missing-premise controls and
multi-size scaling checks pass. Explicit output conversion belongs to step 4.
Do not turn this step into another open-ended census repair pass.

#### Remaining checker routes

An export below is a call to `KernelTermExport::machine`, including calls made
implicitly by `SharedMachineIntegerTerm::Deref`/`AsRef`. Checking the result of a
shared rewrite and then falling back to `.value()` is still a live export.
Producing another term does not make a route an output-only boundary when the
result already supports shared storage (notably pointer indices).

| ID | Caller and boundary | Reproduction and required closure |
| --- | --- | --- |
| R1 | `proof/term_rewrite.rs`: `TermRewrite::integer` → `shared_machine_operand` → `.value()` fallback; `range_endpoint` has the same pattern. Fast checked substitution, also used by fold instantiation. | Replace a variable inside a shared sum by a native `MachineTerm::If`. The shared replacement importer declines and the entire sum is exported. Retain the exact opaque replacement under shared parents; preserve capture avoidance, carrier types, checked refusals and fold scope. |
| R2 | `proof/equality_rewrite.rs`: `rewrite_with_admitted_equality_as_written` → `rewrite_integer_observation` → `shared::rewrite`; the range-endpoint closure repeats this boundary. Fast exact-equality substitution. | An admitted `x == (if b { 1 } else { 2 })` rewrites the Integer observation of shared `x + x`, but exports the source on shared-import failure. Keep the source shared through replacement construction; test an unavailable source, bound variables, read snapshots and both endpoint formats. |
| R3 | `machine_integer/representation.rs::operation_observation`, called by `identity::machine_operation_of_integer_value`, then `comparison_view_through_integer_operations` and checked consumers such as `ProofFacts::shared_operation_reading`. | One shared arithmetic operand and one native opaque operand miss the both-shared branch; `.value()` exports the shared operand. Retain mixed operands in the common operation node, preserving the existing format map and exact range obligations. All-native construction is a separate legitimate input boundary. |
| R4 | `machine_integer/modular.rs::wrapped_equality_at`, called by `rewrite_with_admitted_equality` after the exact rewrite does not apply. Fast explicit rewrite consequence. | Project `to_integer(shared(x + x)) == 0` to its 32-bit word equality. The projection calls `machine.value()`. Its existing 64-node limit counts outer Integer syntax, not nodes inside a machine observation. Retain residue operands and their comparison, preserving width, polarity and the existing admission/refusal rule; do not increase the limit. |
| R5 | `TermRewrite::offset` → `index_bits` → `structural_value`, then `scaled_int32_node`/`scale_int64`. Fast address reconstruction. | Rename `x` to `y` in an `Int32Scaled` offset containing shared `x + x`. Even a successful shared rewrite exports and reimports the result. The destination offset already stores `SharedMachineIntegerTerm`; retain it directly, preserving stride, signedness and the checked unsigned-index narrowing rule. |
| R6 | `ProofFacts::with_checked_rewritten_loads`: mixed observations take `pairs.push((left.value(), right.value()))`; selected unmatched shared pairs can also reach `rewritten_loads::evidence_operand`. Fast checked presentation/evidence matching. | Compare the observation of shared `x + x` with an opaque native conditional. The match correctly refuses, but first exports the shared side. Keep both views through correspondence/refusal; construct native evidence only at a genuine selected native evidence boundary. Preserve binder independence, original snapshots and exact source authority. |
| R7 | Shared indices inside `PointerOffsetTerm::{Int32Scaled,Int64Scaled}`: variable/capture/binder/scope walkers in `reasoning/variable_collection.rs`; `assumptions::collect_pointer_offset_memory_loads`; related offset equality and memory-blind fingerprint adapters. Fast address/dependency checking. | Passing `value: &SharedMachineIntegerTerm` to an `&MachineTerm` helper invokes `Deref` even without an explicit `.value()` call. Direct pointer-variable collection and current-memory dependency collection both export a shared `x + x` index. Use the existing retained carrier/read/scope summaries and operand views; grow index DAGs and vary snapshot/registry/binder state. No change to pointer semantics is needed. |

The R7 call-site review found `collect_pointer_offset_integer_variables`,
`collect_pointer_offset_capture_variables`, `collect_pointer_offset_scope_summary`,
`collect_pointer_offset_binder_variables`, `collect_pointer_offset_bitvector_variables`,
`collect_pointer_offset_memory_loads`, `offsets_equal_with_load_atoms`, and
`hash_memory_blind_pointer_offset`. These are explicit follow-up targets, not
covered by the already-green tests of a scalar observation at the root.

**Audit evidence.** Eight temporary kernel probes used a cold shared `int32`
`Add(x, x)` (one operator, one shared variable used twice) and the native
conditional `if b { 1 } else { 2 }`. Every probe recorded **three machine-export
visits**: general opaque replacement, exact opaque replacement, mixed operation
reconstruction, modular projection, shared-offset renaming, mixed read-evidence
refusal, pointer-index variable collection, and pointer-index memory dependency
collection. Counts are expanded node visits, not distinct input nodes. The
rewrite probes checked that the result changed; the operation/projection probes
checked that a result was produced; the read-evidence probe checked refusal.
The last dependency probe had no loads and still exported the index.
Temporary probes are not retained as tests requiring undesirable behavior;
each migration must replace its reproduction with a zero-export regression.

#### Classified boundaries and retained coverage

- `variable_collection::visit_machine_carrier_leaves`, ordinary shared Integer
  scope collectors, `assumptions::collect_shared_machine_memory_loads`, and
  `proof/facts/selected_atoms` select shared syntax/read/conversion leaves.
  Their native fallback requires an actually native operand. This classification
  excludes the pointer-index edges in R7. Existing cold-DAG, growing-prefix,
  binder and registry tests remain applicable.
- `proof/signed_arithmetic/atom_keys` works on shared syntax and retains its
  explicit conversion/opaque refusals. `proof/integer_arithmetic` keeps machine
  observations as shared atoms; no new boxed checker dependency was found in
  these audited adapters.
- Shared `IntegerTerm::RangeFold` bodies and endpoints retain their shared
  walkers on the supported path. Opaque replacement failures belong to R1/R2,
  not an independent unspecified “fold-output” task. `TermRewrite::bits` may
  materialize a replacement for an existing native `MachineTerm`/`CValue` output,
  including a native machine-fold body. That output-family migration belongs to
  steps 2–3; it does not justify R5's export into an already-shared offset field.
- `NativeComparisonView::integer_condition` retains observations; its
  `boxed_value` call applies only to a written operand or literal. The boxed
  comparison wrappers still serve native-input converse readings, Surface
  spelling/planning (`observed_native_surface_comparison` and premise spelling
  in `surface/proof/smart_closures.rs`), and `ProofObligation::verification_condition`
  production through `canonical_observation_form`. The latter also serves the
  frontend's `verify_kernel_standard_theorem_axiom` declaration check in
  `surface/proof/pure_theorems.rs`; it is not merely a printer. Keep these
  frontend/production/output boundaries classified for steps 2/4;
  the removed condition-dispatcher export must not return.
- `eval::canonicalized_offset_index_term` receives an owned native term at a
  producer boundary. `identity::boxed_machine_operation_of_integer_value` and
  `native_comparison_through_integer_operations` are test-only references.
- `resource_tracker::{reads_of_proposition,reads_any_resource,version_mismatch}`
  reach the old Integer read collector from diagnostic history/rendering,
  including diagnostic capture in Surface's proof object. The missing-fold-guard
  helper is `surface/proof/proof_object/resource_steps.rs::describe_missing_fold_guards`.
  These are output/diagnostic callers, not evidence for checking a claim.
- `IntegerTerm::max_variable` still has no in-repository callers. It is public;
  its existence alone is not a live checker dependency or proof of external API
  compatibility for deletion.

The audit reran the existing shared rewrite, source, collector, atom, read-evidence
and registry controls: 59 syntax/rewrite controls and 13 registry/dependency
controls passed. This scoped evidence does not close the reproduced gaps above.

**Delivery order:** retain opaque replacements in R1/R2; close mixed operation
construction R3; migrate modular rewrite projection R4; migrate address walkers
R7 and address reconstruction R5; finish mixed read-evidence matching R6. Keep
one coherent PR open at a time. R1/R2 should reuse the exact native-leaf boundary
introduced for tagged addresses, rather than redesign opaque term families.

### 2. Finish expression producers

The concrete starting point is `kernel/spec/shared_machine/signed.rs`: it
currently prepares one signed operation over available values and declines nested
signed expressions. `shared_machine.rs` also retains deferred evaluator paths.

- [ ] Enable nested signed construction with shared obligation operands, after
  step 1's checker boundary is closed.
- [ ] Inventory the remaining deferred/partial operations and C/Rust execution
  producers in the existing evaluator, and migrate those still rebuilding
  shared expressions through legacy trees.
- [ ] Preserve evaluation order, scoped obligations, conversion rules and
  undefined-behavior refusals. Keep positive and negative cases for shifts,
  division/remainder, short-circuit conditions and quantified obligations.

**Done when:** the inventoried expression producers construct common nodes and
retain those nodes in obligations; execution and checking do not repeatedly
export their prefixes. Keep
`forward_conversion_requires_symbolic_argument_definedness` as a negative
control: claim completion must not bypass evaluation obligations.

### 3. Finish existing term families without redesigning their semantics

`KernelTermNode::Legacy` and `LegacyBool` are explicitly temporary bridges.
`MemoryLoad` still has a native `Pointer` address payload. These require an
explicit representation disposition, not an assumption that a wrapper alone
finishes the split.

- [ ] Enumerate the existing legacy import/export arms and their live producers
  and consumers. Cover Boolean conditions, algebraic values, binders/folds,
  read addresses and complete pointer values already supported at the baseline.
- [ ] Give remaining expression payloads typed common nodes/operand views,
  preserving all existing identity and metadata; remove their generic legacy
  bridges and duplicate expression storage as their consumers migrate.
- [ ] Distinguish expression children from legitimate opaque semantic atoms,
  such as a memory snapshot identity or execution event identity. Such atoms may
  remain opaque; an opaque wrapper around an expression tree is not a substitute
  for migrating its children.

**Done when:** existing term families use the common representation, with exact
construction/import/raise/lower tests and no generic legacy expression bridge
on their live paths. Existing typed APIs may remain as views of the common DAG;
independent parallel expression trees may not.

Preserving the current complete `CPointerValue` payload is in scope. Designing a
new public `CPointer` constructor, changing its fields or changing C provenance
semantics is not a prerequisite. Do not declare issue #2179 resolved by this
representation work. Frontend ASTs and statement evaluators may remain distinct
because they represent source/evaluation information, not a second kernel term
model; states and resources need not become expression nodes.

### 4. Close the common boundary and declare the split complete

- [ ] Route supported common nodes through shared structural lowering and
  raising. Remove exports to the old speller and duplicate family-specific
  expression conversion paths.
- [ ] Make fact/goal term operands use that common path while preserving their
  proposition, binder and resource structure. A separate fact renderer may
  still have a tracked defect; it must not require another expression model.
- [ ] Delete obsolete bridges and duplicate storage. A compatibility *name*
  such as `ContractExpression = SurfaceTerm` may remain if it denotes the same
  type and carries no alternative behavior; renaming every caller is not a
  completion requirement.
- [ ] Run the final validation below, publish the closed boundary inventory,
  and explicitly mark this representation milestone complete.

**Split complete when all four steps are closed:** common term-level round trips
are exact, checker and producer paths use the common representation, obsolete
expression bridges are removed, and the integration gate passes. The remaining
spellability work below does not silently extend this finish line.

## Final validation and scope control

Retain exact raise/print/parse/lower tests for the existing common term families,
including casts, nested arithmetic, binders, reads and complete pointer payloads.
Test actual obligation discharge and refusal, successful and unsuccessful
checker decisions, historical identities and branch isolation. Run deterministic
scaling tests across growing DAGs, changed contexts and unrelated facts.

Use `scripts/check.sh` as the integration gate; do not substitute a nightly run,
raise limits or weaken proofs. Run the regular-corpus fact-stability audit with
zero differences and record a separate spellability census with its remaining
misses. A globally empty census is **not** required to close this split.

A new census finding blocks the migration only if a reproduction demonstrates
that it breaks one of the closure criteria above: common representation,
term-level round-trip identity, rule parity or scaling. Name that exact route and
test. A failure in existing fact-to-expression synthesis is not automatically
proof that another term-family migration is needed. New regressions introduced
by the migration still need fixing; separating milestones does not excuse them
or authorize placeholders, spelling searches or fact-dependent lowering.

The tagged-address consumer now retains shared operands, including mixed residual
tags containing an explicit native opaque input. Those inputs use the existing
`KernelTerm::Legacy` boundary with a producer identity that preserves their exact
payload; this does not migrate opaque pointer expression families in step 3.
`wide_observation_keeps_tagged_address_equality_rules` proves that with
`x == address(p) + 1`, the checker still refutes `x == x + 1` without a machine
export, and preserves the negated result, source withdrawal and branch isolation.
Tag-form memoization is scoped to the fact/read generation, decision mode and
nesting depth; cached answers retain their source evidence. Multi-size growing
DAG tests cover repeated misses and reuse of checked prefixes.

The completed checker audit above now supplies step 1's concrete R1–R7 closure
list. Start with opaque replacement handling in R1/R2, then follow its delivery
order before proceeding through steps 2–4. Do not resume the
census backlog as the default next task.

## Spellability follow-up — outside the split's finish line

Keep these visible without reopening completed migration steps:

- The focused volatile census reports a smart-step `PointerValueEqual` miss in
  `update_pointer_cell.contract`, rendered `replacement == cell[0]`. The fixture
  verifies. Raising currently selects expressions from the underlying pointers;
  the exact original-versus-relowered field mismatch has not yet been isolated.
  Investigate it as a fact-spelling defect unless it demonstrates a closure
  blocker under the rule above. Do not assume it requires a new CPointer design.
- The earlier `design/charon-trial/held-values` census reported `unfold`
  equations with a `match` right side and a call precondition instance recorded
  before its result. Reproduce before claiming they remain current; preserve
  `charon_held_value_locals_are_spelled_by_name` coverage.
- Other introduced-value names, missing fact syntax, total fact/goal spelling
  and a globally zero-miss census remain the broader unspellable-facts project.
  They are not extra unchecked steps in the representation milestone.

Latest landed evidence (#2492, before this documentation revision): the full
gate passed 7,663 unit/API tests, 58 examples and 5,107 Markdown fixtures. Both
regular corpora passed fact-stability auditing with zero differences. The
focused volatile census passed 11 fixtures and reported the one miss above.
These are scoped measurements, not evidence that the split is already complete.

## Delivery and history

Land coherent tested slices in small PRs, one open PR per thread, with auto-merge
enabled. Check queue state before updating a head and verify pushed work reached
upstream after merging. Each PR should identify the checklist boundary it closes
and remove stale active entries instead of appending another chronological
progress narrative. Ask for semantic decisions, not routine ordering.

The [pre-revision roadmap](https://github.com/clicklang/click/blob/93c5fe74cd6ff161782b65a9709ffe57cd3eca76/roadmap/unspellable-facts.md)
preserves detailed consumer migrations, tests, constraints and checkpoint PRs.
The [older handoff](https://github.com/clicklang/click/blob/1e4e07c98fb5354cf6a14ce985c08d5af95f286c/roadmap/unspellable-facts.md)
preserves the original pointer-read WIP, semantic decisions and dropped trials.
Neither historical checklist is the active work queue.
