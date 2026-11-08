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
Close the finite audit inventory below. For each route record its caller, its role (checking, production,
output, test reference or unused), and the deletion or regression that closes it.
A textual accessor occurrence alone is not evidence of a checker dependency.

| Route/group | Evidence and required closure |
| --- | --- |
| Wide comparison dispatch — closed | `decision.rs` sends retained operands to tagged-address reasoning. Residual tag arithmetic stays shared, exact source premises and selected native read transport are preserved, and the dispatcher no longer exports shared operands. Fixed-size atoms and already-native comparisons retain their native rules. |
| Memory-resolution bounds — closed | `recorded_less_equal_candidates` retains operand views and the order index retains original true signed `<`/`<=` source membership. Memory equality reads shared arithmetic and selected native read leaves without exporting endpoints; parity, withdrawal, direction and DAG scaling controls cover this boundary. |
| Mixed operands and reconstruction | Close the remaining exact-equality rewrite, fold-output, modular and operation-reconstruction boundaries identified in the previous audit. Distinguish a genuinely native input/output from exporting a shared operand just to inspect it. |
| Dependency and atom walkers | Confirm remaining guarded legacy branches retain shared inputs and selected read authority. Include growing prefixes, cold DAGs and registry/branch changes. |
| Output and dead helpers | `resource_tracker::collect_integer_node_reads`, the missing-fold-guard diagnostic and Surface bound-planning adapters were classified as output/planning. `IntegerTerm::max_variable` had no in-repository callers. Recheck callers; do not reopen all their checker migrations based on their names alone. |

- [x] Close the memory-resolution endpoint export.
- [x] Close the wide-comparison export after migrating its tagged-address consumer.
- [ ] Classify and close each remaining audit group above; retain a short final
  inventory of legitimate frontend/output boundaries.
- [ ] Remove the obsolete checker adapters and retain no-export regressions.

**Done when:** no checker exports a shared expression to a boxed tree to inspect
it or decide a premise; native/shared rule parity, missing-premise controls and
multi-size scaling checks pass. Explicit output conversion belongs to step 4.
Do not turn this step into another open-ended census repair pass.

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

Next finish step 1's bounded caller audit, especially exact-equality rewriting
and operation reconstruction, then proceed through steps 2–4. Do not resume the
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
