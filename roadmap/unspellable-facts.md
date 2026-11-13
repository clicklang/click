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

Baseline for this revision: `1dcc52be1`, including merged PR #2581.

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

**The split is not complete.** The remaining checker boundaries in the
compiler-assisted inventory are closed below. Execution producers, generic
legacy payloads and the common raise/lower boundary remain. Nested signed arithmetic
construction is enabled, as recorded in step 2.
These are concrete migration boundaries,
not a count of every remaining defect in the verifier.

The previous document interleaved open boxes with later paragraphs completing
parts of them. Its old unchecked lists and historical accessor counts must not
be treated as a current to-do list. The detailed evidence is preserved in
[the pre-revision roadmap](https://github.com/clicklang/click/blob/93c5fe74cd6ff161782b65a9709ffe57cd3eca76/roadmap/unspellable-facts.md).

## Authorized delivery sequence

The next ten work packages each receive at least one PR. A package is closed
only when its named boundaries and regression coverage are complete; these are
not ten aliases for partial progress on one boundary. Keep one PR open at a time.

| Chunk | Work package | State |
| --- | --- | --- |
| 1 | Let bindings and local value handoffs | Merged in [PR #2617](https://github.com/clicklang/click/pull/2617); specification bindings retain shared values through selected lookups, with shadowing and snapshot scope preserved. |
| 2 | Symbolic conditional joins | Merged [PR #2638](https://github.com/clicklang/click/pull/2638). Typed guards and shared arms survive checking, transport, snapshot matching and Surface spelling. The full gate passed 7,294 unit/API tests, 5,240 fixtures and all examples; its 15m54s run exceeded the ten-minute target. The final conditional-equality follow-up passed 1,884 selected checks, including all scaling, Rust import and expansion tests. Its full-corpus fact-stability audit passed all 5,240 fixtures with zero differences. |
| 3 | Pure-function arguments and results | In progress. [PR #2643](https://github.com/clicklang/click/pull/2643) retained shared machine values during argument assembly. [PR #2647](https://github.com/clicklang/click/pull/2647) retains them in call payloads and migrates argument collection, rewriting, alpha keys, congruence and fold-read consumers. Typed semantic application identity is separate from exact producer payloads; numeric indexes share native/retained call identities, and comparison cycle guards permit narrow-to-wide checking. Repeated native/shared readings do not accumulate payload versions. Common machine call result roots and remaining result consumers are still open. |
| 4 | Mixed-width arithmetic and casts | Implemented as subchunks 4a–4j below, one PR per subchunk. Numeric producers retain shared operands and results within the existing supported profile. General call and nonnumeric compatibility boundaries belong to the remaining packages; the previous combined branch stays unmerged reference material. |
| 5 | C/Rust execution result carriers | Open |
| 6 | Folds, binders and algebraic matches | Open |
| 7 | Complete pointers and read addresses | Open |
| 8 | Remaining Boolean and opaque expression payloads | Open |
| 9 | Unified raising/lowering and certificate boundaries | Open |
| 10 | Duplicate storage removal and final closure | Open |

## Chunk 3: machine-valued pure-function results

Finish the remaining machine-valued call-result boundaries in six sequential
PRs, preparing consumers before switching the evaluator. Pointer, algebraic, Boolean and
floating-point result families remain in their own packages. Preserve existing call
semantics, exact producer metadata, proof/refusal behavior and fact stability;
do not introduce search strategies, indexes or larger budgets to compensate for
representation changes.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 3a | Common result roots | Typed common calls preserve the function, ordered arguments, result type and exact opaque producer payloads; native/shared numeric inputs agree. |
| 3b | Numeric consumers | Observations, casts and arithmetic retain common machine call operands without prefix exports. |
| 3c | Comparison and fact matching | Existing comparison/equality keys preserve native/shared rules, source premises and refusals. |
| 3d | Rewriting and transport | Substitution, rewriting, dependencies and snapshot handling retain common call roots and their arguments. |
| 3e | Surface boundary | Calls round-trip through raising, lowering and certificate paths with exact term identity. |
| 3f | Producer switch and closure | Actual call evaluation returns common machine roots; nested calls and result handoffs retain them, and obsolete adapters for this boundary are removed. |

3a adds the explicit common-root constructor and machine export route without
switching the evaluator or admitting calls into the shared machine operand
fragment. Opaque argument descriptors use the retained application's exact
payload identity, separately from semantic application equality. Consumers are
prepared in the following slices before producer activation.
[PR #2686](https://github.com/clicklang/click/pull/2686) merged and its pushed
commit was verified on upstream. All 1,536 selected tests (including all 1,525
scaling tests) and all 5,275 regular fixtures passed, with zero fact-stability
differences.

3b admits common integer call roots to numeric operand views, preserving their
root in mathematical observations and retaining argument handles in the cached
compatibility reading. Casts and arithmetic retain their operands and ordinary
definedness debts. The native 128-bit call-root refusal includes identity casts;
the shared shortcut reports the same type error without exporting arguments.
[PR #2690](https://github.com/clicklang/click/pull/2690) merged and its pushed
commit was verified on upstream.

3c gives common call observations the existing native typed application key,
without replacing their exact producer roots. Comparison sources retain their
written premises, polarity and branch authority. The existing observation memo
walks selected children once; repeated queries do not scan accumulated facts.
[PR #2691](https://github.com/clicklang/click/pull/2691) merged and both pushed
commits were verified on upstream. It also admits common calls to the existing
typed congruence registration. The final fixture audit passed with zero differences.

3d retains common call roots through checked substitutions, exact rewrites and
pointer-index transport. Unchanged leaves keep exact payload identity; changed
calls rebuild common arguments. Native/shared selected-source matching uses the
existing typed application identity. Pure-call arguments retain their original
snapshots under transport, following the native rule. No new search or index is
introduced. [PR #2694](https://github.com/clicklang/click/pull/2694) merged and its
pushed commit was verified on upstream. All 1,699 selected regressions and all
5,275 regular fixtures passed, with zero fact-stability differences.

3e imports native integer calls through the common call constructor and retains
nested numeric argument structure at the Surface boundary. Raising an ordinary
machine call spells its selected integer type explicitly, including a signed
reading of an unsigned call. Native 128-bit call identity-cast refusals remain
unchanged. Source roundtrips cover all ten integer result types, nested calls,
casts and arithmetic; certificate checks preserve definedness and selected
premises. The actual evaluator producer switch is the remaining 3f slice.

## Chunk 4: one producer boundary per PR

Chunk 4 migrates existing numeric producers to retain `KernelTerm` operands and
results. It preserves language semantics, definedness obligations, exact fact
identity, accepted proofs and refusals. It does not add arithmetic capabilities
or redesign proof search.

The previous combined branch is reference material only. Extract and review each
subchunk independently on a fresh branch from current upstream after the previous
PR merges. Do not merge the combined branch or carry its accumulated fixes into
every subchunk. Later chunks remain parked. Each row receives its own PR; split a
row further if it cannot remain a small, independently validated change.

| Subchunk | Producer boundary | Scope |
| --- | --- | --- |
| 4a | Same-type integer casts | Retain identity through casts that do not change integer type; preserve named reads and snapshots. |
| 4b | Signedness conversions | Existing same-width signed/unsigned conversions for 8/16/32/64-bit values. |
| 4c | Widening casts | Existing sign extension and zero extension through 64 bits. |
| 4d | Narrowing casts | Existing truncation and low-word conversions through 64 bits. |
| 4e | Mixed-width arithmetic | Existing integer promotions and usual arithmetic conversions through 64 bits; retain converted operands and results. |
| 4f | Explicit narrow arithmetic | Existing annotated 8/16-bit operations with narrow results, distinct from ordinary promoted arithmetic. |
| 4g | C shifts | Retain operands with independently typed shift counts; preserve C definedness obligations. |
| 4h | Rust shifts | Preserve existing Rust-specific shift behavior and obligations. |
| 4i | Bitwise operations | Existing numeric AND, OR, XOR and NOT, including narrow NOT and required tag side facts. |
| 4j | Supported 128-bit paths | Existing 128-bit conversions and supported arithmetic/bitwise paths; unsupported operations remain unsupported. |

The 4a audit confirms that the existing unary and cast-chain paths already
retain same-type shared integer results. Its PR adds exact-root coverage across
all ten integer formats, registered-read snapshot controls, a changed-type
negative control, and no-export scaling over 16/32/64 casts. Native inputs retain
their existing compatibility boundary. Focused tests and all 1,507 scaling tests
passed; the unchanged `preserve_apply_names_its_missing_viewable.md` passed its
fact-stability audit with zero differences. [PR #2674](https://github.com/clicklang/click/pull/2674)
merged and its pushed commit was verified on upstream.

Subchunk 4b retains already-shared operands in same-width signedness casts at
8, 16, 32 and 64 bits. It preserves the native conversion table's exact written
terms, including inverse 32-bit sign pairs and selected 64-bit extension roots.
Opaque native operands retain shared cast parents after their input boundary;
general calls outside the shared machine fragment keep the compatibility path.
Fixed-size cast-variable comparison guards preserve their native spelling so
cited quotient/remainder bounds continue to match. Tests compare exported terms
against native conversions and check no-export scaling at 16/64/256 casts.
[PR #2677](https://github.com/clicklang/click/pull/2677) merged; both pushed
commits were verified on upstream. All 5,273 regular fixtures and all 1,509
scaling tests passed, with zero fact-stability differences.

Subchunk 4c retains already-shared operands through the 24 widening conversions
among signed/unsigned 8/16/32/64-bit types. It reuses the same selected-root
constructor as 4b, including the native conversion table's generic casts and
32-to-64-bit extension nodes. Exact-term parity covers constants, opaque leaves,
arithmetic, and prior conversion roots; growing-prefix scaling checks retained
children and zero exports at 16/64/256 steps.
[PR #2678](https://github.com/clicklang/click/pull/2678) merged and its commit was
verified on upstream. All 1,511 scaling tests and the regular fixture corpus
passed, with zero fact-stability differences.

Subchunk 4d retains shared results through the 24 narrowing conversions among
signed/unsigned 8/16/32/64-bit types, using the existing generic truncation and
64-to-32-bit low-word constructor rules. Exact-native parity covers boundary
constants, opaque leaves, arithmetic and prior cast roots; 16/64/256-step scaling
checks growing shared prefixes without exports. The existing listed-equality
rewrite strategy also recognizes retained machine observations, preserving the
`snprintf` length proof without changing its source or proof. Expansion/replay,
missing-premise and constant-work admission controls cover that representation
boundary. [PR #2679](https://github.com/clicklang/click/pull/2679) merged; both
pushed commits were verified on upstream. All 1,513 scaling tests and all 5,274
regular fixtures passed, with zero fact-stability differences.

Subchunk 4e retains ordinary arithmetic operands through the existing integer
promotions and usual arithmetic conversions for 8/16/32/64-bit formats. Deferred
addition, subtraction, multiplication, division and remainder reuse the shared
cast constructors and retain their result and definedness obligations. Shifts
keep their separate boundary. Exact native result/domain parity covers all 64
format pairs, mixed native/shared operands, constants and opaque leaves; growing
prefixes check deterministic work and zero exports.
[PR #2680](https://github.com/clicklang/click/pull/2680) merged and its pushed
commit was verified on upstream. All 1,514 scaling tests and all 5,274 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4f retains annotated 8/16-bit addition, subtraction and multiplication
with their existing modular result formats. Operand admission accepts the same
format and fitting unsuffixed int32 literals; other operand types retain the
compatibility path. Literal folding follows the native narrow constructor, and
no new domain obligation is introduced. Exact parity, nested evaluator and
16/64/256-step retained-child scaling tests cover the boundary.
[PR #2681](https://github.com/clicklang/click/pull/2681) merged and its pushed
commit was verified on upstream. All 1,515 scaling tests and all 5,274 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4g retains C-style shift values and independently promoted counts.
Count bounds keep the full wide operand before the operation selects its low
word. Result children use the native importer's operator reading while the
count guards retain the independently promoted type. Signed left shifts keep their nonnegative-value and result-fit obligations.
Shared int64 comparisons reuse the native constructor's root-width bound folding,
so those obligations match the native producer. The affine boundary reads a
false retained disequality as its equality, and certificate source collection
retains the written operands under negation. Tests cover all 64 value/count
format pairs, boundary counts including 2^32, native/shared and opaque operands,
native shared-root identity, explicit bound certificates and expansion/replay,
and deterministic growing value/count chains with zero exports.
[PR #2682](https://github.com/clicklang/click/pull/2682) merged and its pushed
commit was verified on upstream. All 1,517 scaling tests and all 5,275 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4h retains Rust shift operands and results through the existing unsigned
left-shift conversion, signed right-shift promotion and conversion back to the
original type. The count bound uses that original 8/16/32/64-bit width while
sharing 4g's independent count handling. Native term/domain and shared-root
identity parity, nested evaluator/refusal controls and growing chains cover the
Rust boundary. [PR #2683](https://github.com/clicklang/click/pull/2683) merged
and its pushed commit was verified on upstream. All 1,518 scaling tests and all
5,275 regular fixtures passed, with zero fact-stability differences.

Subchunk 4i retains ordinary numeric AND, OR, XOR and NOT through 64 bits,
including their usual promotions, and annotated narrow bitwise operations.
Native mask folding, XOR component ordering/cancellation and double-NOT rules
are preserved. Tag-clearing equalities remain separate side facts; pointer
provenance records retain their explicit compatibility boundary. Alignment
recognition, its bounded certificate reader and the planner accept the retained
mask equality; existing equality keys normalize signed/unsigned 64-bit literals
by their bits. Standard-theorem declaration matching uses the existing exact
proposition identity across native and retained comparisons.
[PR #2684](https://github.com/clicklang/click/pull/2684) merged and both pushed
commits were verified on upstream. All 7,409 non-corpus library tests (including
1,522 scaling tests) and all 5,275 regular fixtures passed, with zero
fact-stability differences.

Subchunk 4j retains conversions involving 128-bit integer formats and the
existing bounded wide arithmetic profile: signed 128-bit multiplication and
same-format signed/unsigned 128-bit division and remainder. Results retain their
mathematical source; overflow and C-defined divisor requirements remain
obligations, never assumed facts. Typed 128-bit reads retain their kind and
snapshot through casts and integer observations. Unsupported wide addition,
subtraction, unsigned multiplication, mixed division, shifts and bitwise
operations remain unsupported. General calls and nonnumeric compatibility
boundaries remain explicit; completing chunk 4 does not complete the overall
KernelTerm/SurfaceTerm migration. Native parity, refusal and snapshot controls,
nested evaluation and two deterministic growth tests pass. All 1,571 selected
regressions (including all 1,524 scaling tests) and all 5,275 regular fixtures
pass, with zero fact-stability differences.

For each PR:

- State the one producer path being migrated and compare its native and retained
  results, including types, casts and ordinary proof obligations.
- Keep existing C and proof fixtures unchanged. In particular,
  `preserve_apply_names_its_missing_viewable.md` must continue to pass.
- Cover positive, refusal and scope/snapshot cases relevant to that path, plus
  no-export and deterministic scaling checks where representation work requires
  them. Run all scaling tests for performance-sensitive changes and the ordinary
  required gate through the repository workflow.
- Fix a blocking representation mismatch at its smallest existing consumer
  boundary. Do not compensate with new search strategies, broader fact indexes,
  increased budgets or altered proofs. If the producer cannot yet preserve the
  existing behavior, retain its compatibility path and reduce the PR scope.
- Record actual validation and merge status. Completion of one row does not
  imply completion of the rest of chunk 4.

## Ordered closure checklist

### 1. Close the remaining checker boundaries — closed

Finish the checker consumers before enabling the remaining shared producers.
The original bounded caller audit was recorded at `fe8c6d931` (PR #2500).
Its specific R1–R7 reproductions were insufficient: disabling the implicit
native conversions at `b247d7499` (PR #2517) exposed additional live callers.
The final pass removes both `SharedMachineIntegerTerm` native conversion traits
permanently, migrates their checker consumers, and makes the remaining output
conversions explicit. Production compilation therefore enforces this boundary.
The closure is the finite checker inventory, not every producer or legacy term
family. A textual accessor occurrence alone is not evidence of a checker dependency.

| Route/group | Evidence and required closure |
| --- | --- |
| Wide comparison dispatch — closed | `decision.rs` sends retained operands to tagged-address reasoning. Residual tag arithmetic stays shared, exact source premises and selected native read transport are preserved, and the dispatcher no longer exports shared operands. Fixed-size atoms and already-native comparisons retain their native rules. |
| Memory-resolution bounds — closed | `recorded_less_equal_candidates` retains operand views and the order index retains original true signed `<`/`<=` source membership. Memory equality reads shared arithmetic and selected native read leaves without exporting endpoints; parity, withdrawal, direction and DAG scaling controls cover this boundary. |
| Mixed operands and reconstruction — closed | R1/R2 source and replacement matching, R5 pointer-index reconstruction and R6 mixed read-evidence matching retain shared operands, including refusal paths. Native evidence comes from selected native leaves or stores. |
| Dependency and atom walkers — closed | Ordinary scalar carriers, selected atoms, shared memory dependencies and R7 pointer-index walkers retain their operands. |
| Output and dead helpers — classified | See the separate boundary inventory below. Native output construction, diagnostics and test references do not establish that a checker inspected a shared tree. |

- [x] Close the memory-resolution endpoint export.
- [x] Close the wide-comparison export after migrating its tagged-address consumer.
- [x] Classify the remaining audit groups and record legitimate native/output boundaries.
- [x] Close R1/R2 opaque source and replacement matching with retained operands.
- [x] Close R3 mixed operation construction with retained native operands.
- [x] Close R4 modular equality projection with retained residue operands.
- [x] Close R7 pointer-index dependency, scope, comparison and fingerprint walkers.
- [x] Close R5/R6 with parity, refusal, no-export and deterministic scaling regressions.
- [x] Remove the obsolete checker adapters and retain no-export regressions.

**Done when:** no checker exports a shared expression to a boxed tree to inspect
it or decide a premise; native/shared rule parity, missing-premise controls and
multi-size scaling checks pass. Explicit output conversion belongs to step 4.
Do not turn this step into another open-ended census repair pass.

#### Final retained checker boundary pass

The starting audit at `fe3690b72` produced 106 diagnostics with native
`Deref`/`AsRef` disabled. Both traits are now removed, and production compilation
passes. Native output callers explicitly request structural output; the old
`scaled_values` traversal is named `native_scaled_values_for_output` and has no
checker callers.

The remaining scaled-index consumers retain operands through:

- Selected-read, root-variable, initialized-byte and guarded-cell inspections;
  signed/unsigned element-bound guards and exact unsigned range membership.
- Scalar and pointer equality rewriting, canonical base-root construction,
  binder substitution, shallow load expansion and equality-fact atom indexing.
- Algebraic scalar-payload traversal, resource-read collection and load
  footprints. Footprints memoize shared nodes by depth, preserving the existing
  depth refusal and source-snapshot/checked-width requirements.
- Arithmetic certificate payload, identity, hashing, translation and alignment
  checks. Occurrence budgets and unsupported-operator refusals remain unchanged;
  a compact DAG does not admit a formerly oversized certificate.
- Wide range-normalization coordinates and candidate keys. Snapshot-sensitive
  memoized fingerprints replace exported endpoint trees; candidates still go
  through the ordinary merge rule. The selected coverage cursor keeps a wide
  displacement without constructing a temporary native range.
- Recorded equality-class input and members. The existing enumeration is
  unchanged, including native source ordering and duplicate handling; it is
  **not** newly classified as a bounded fast lookup. Only its native reference
  adapter remains test-only. Resource-normalization candidate lookup also keeps
  equality-class members retained through its byte/element coordinate keys. Existing scan bans also reject the retained APIs.
- Pointer reassociation: the exact nonoverflow premise is indexed from the
  explicitly cited conditions, with collision verification and no ambient
  lookup. Guard collection still constructs native planner outputs explicitly.

Remaining explicit output boundaries include diagnostic/rendering and Surface
synthesis, native planner segment and instantiation arguments, comparison
prefilter outputs, and the havoc write-set identity producer. These are not
permission to export within a checker; their payload migrations belong to
steps 2–4. Bounded planner comparisons and source-capability inspection also
retain shared operands before applying their existing refusal limits.

Regression coverage includes native/shared behavior, missing and opposite
premises, source withdrawal, certificate size refusal, snapshot and width
checks, and cold repeated-child DAGs at 16/64/256 nodes with no machine exports.
The full local gate passed 7,198 unit/integration tests and all four fixture
harnesses in 11m42s (over the ten-minute target). A subsequent production-only
compile exposed one remaining native equality-class adapter caller in resource
normalization; that caller is migrated above. The final production build passed;
all 1,520 selected normalization, boundary and nonignored scaling tests passed,
as did all 42 documentation tests. Before/after `transport_wide_viewable`
fact-stability runs both passed with zero fact-dependent lowerings. The final
adapter follow-up received these focused checks rather than a second full gate.

#### Checker route inventory

An export below is a call to `KernelTermExport::machine`, including calls made
implicitly by `SharedMachineIntegerTerm::Deref`/`AsRef`. Checking the result of a
shared rewrite and then falling back to `.value()` is still a live export.
Producing another term does not make a route an output-only boundary when the
result already supports shared storage (notably pointer indices).

| ID | Caller and boundary | Reproduction and required closure |
| --- | --- | --- |
| R1 — closed | `proof/term_rewrite.rs`: `TermRewrite::integer` → `shared_machine_operand` → `.value()` fallback; `range_endpoint` has the same pattern. Fast checked substitution, also used by fold instantiation. | Replace a variable inside a shared sum by a native `MachineTerm::If`. The shared replacement importer declines and the entire sum is exported. Retain the exact opaque replacement under shared parents; preserve capture avoidance, carrier types, checked refusals and fold scope. |
| R2 — closed | `proof/equality_rewrite.rs`: `rewrite_with_admitted_equality_as_written` → `rewrite_integer_observation` → `shared::rewrite`; the range-endpoint closure repeats this boundary. Fast exact-equality substitution. | An admitted `x == (if b { 1 } else { 2 })` rewrites the Integer observation of shared `x + x`, but exports the source on shared-import failure. Keep the source shared through replacement construction; test an unavailable source, bound variables, read snapshots and both endpoint formats. |
| R3 — closed | `machine_integer/representation.rs::operation_observation`, called by `identity::machine_operation_of_integer_value`, then `comparison_view_through_integer_operations` and checked consumers such as `ProofFacts::shared_operation_reading`. | One shared arithmetic operand and one native opaque operand miss the both-shared branch; `.value()` exports the shared operand. Retain mixed operands in the common operation node, preserving the existing format map and exact range obligations. All-native construction is a separate legitimate input boundary. |
| R4 — closed | `machine_integer/modular.rs::wrapped_equality_at`, called by `rewrite_with_admitted_equality` after the exact rewrite does not apply. Fast explicit rewrite consequence. | Project `to_integer(shared(x + x)) == 0` to its 32-bit word equality. The projection calls `machine.value()`. Its existing 64-node limit counts outer Integer syntax, not nodes inside a machine observation. Retain residue operands and their comparison, preserving width, polarity and the existing admission/refusal rule; do not increase the limit. |
| R5 — closed | `TermRewrite::offset` → `index_bits` → `structural_value`, then `scaled_int32_node`/`scale_int64`. Fast address reconstruction. | Rename `x` to `y` in an `Int32Scaled` offset containing shared `x + x`. Even a successful shared rewrite exports and reimports the result. The destination offset already stores `SharedMachineIntegerTerm`; retain it directly, preserving stride, signedness and the checked unsigned-index narrowing rule. |
| R6 — closed | `ProofFacts::with_checked_rewritten_loads`: mixed observations take `pairs.push((left.value(), right.value()))`; selected unmatched shared pairs can also reach `rewritten_loads::evidence_operand`. Fast checked presentation/evidence matching. | Compare the observation of shared `x + x` with an opaque native conditional. The match correctly refuses, but first exports the shared side. Keep both views through correspondence/refusal; construct native evidence only at a genuine selected native evidence boundary. Preserve binder independence, original snapshots and exact source authority. |
| R7 — closed | Shared indices inside `PointerOffsetTerm::{Int32Scaled,Int64Scaled}`: variable/capture/binder/scope walkers in `reasoning/variable_collection.rs`; `assumptions::collect_pointer_offset_memory_loads`; related offset equality and memory-blind fingerprint adapters. Fast address/dependency checking. | Passing `value: &SharedMachineIntegerTerm` to an `&MachineTerm` helper invokes `Deref` even without an explicit `.value()` call. Direct pointer-variable collection and current-memory dependency collection both export a shared `x + x` index. Use the existing retained carrier/read/scope summaries and operand views; grow index DAGs and vary snapshot/registry/binder state. No change to pointer semantics is needed. |

The R7 call-site review found `collect_pointer_offset_integer_variables`,
`collect_pointer_offset_capture_variables`, `collect_pointer_offset_scope_summary`,
`collect_pointer_offset_binder_variables`, `collect_pointer_offset_bitvector_variables`,
`collect_pointer_offset_memory_loads`, `offsets_equal_with_load_atoms`, and
`hash_memory_blind_pointer_offset`. These now use retained operands; their tests enter through scaled pointer
indices, rather than only a scalar observation at the root.

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

#### Opaque-source and replacement migration

The general and exact-equality walkers now retain an opaque native replacement
under shared arithmetic, including range endpoints. Variable, read and conversion
leaf callbacks use the same exact native-leaf boundary. An unchanged retained
leaf keeps its identity, so an absent source does not manufacture a rewrite.
Cold DAG regressions cover 16, 64 and 256 shared operators in both rewrite routes,
with zero exports and near-linear deterministic work; parity controls cover
whole-expression replacement, missing sources and both endpoint formats.

R1/R2 are **closed**. `proof/machine_source_match.rs` builds query-local
structural keys for the selected source and shared goal. Each shared node is
visited once; parent keys use child IDs, while opaque leaves use the existing
native equality rule. These keys never replace term identities or snapshot
authority. Source imports are retained per carrier; native leaf hashing is
charged, including its payload cost. Neither matching nor a miss exports the
shared expression.

Exact equality rewriting uses the same matcher for its existing canonical-read
comparison. Its numeric address/mask comparison now uses operand views and keeps
its existing operand-order rule. Controls cover changed snapshots, absent
sources, native and shared source inputs, and the deliberate refusal of composite
sources beneath C-item fold binders. Scaling grows both native source length and
shared goal depth at 16, 64 and 256 nodes, for hits and misses in both routes.
The original opaque-source fallback is removed.

R3 is **closed**. Mixed operation construction retains the shared operand and
imports only the explicit native operand. Opaque native composites stay intact
so the checked exact-reading path retains their original observation identity.
The all-native input boundary, format map, literal spelling, unsupported
128-bit operators and exact range premises are unchanged. Controls cover eight
supported formats, both operand orders and all three ring operations, plus
missing lower/upper premises and opaque composite identity. Cold shared DAGs at
16, 64 and 256 operators require constant deterministic construction work and
zero exports.

R4 is **closed**. The bounded modular equality projection carries native or
shared residue operands through construction and uses the shared comparison
view. It never exports an observed shared machine tree. Existing word folding
is reused; narrow operators retain their literal-only folding rule. Width,
equality polarity, the 64 outer-Integer-node limit, and the requirement for an
observation remain unchanged. Native-spelling parity covers all supported
formats, negation, ring operations, repeated and opaque operands; controls cover
refusals and the exact node-limit boundary. A checked equality-rewrite regression
uses a signed observation to rewrite its unsigned residue without export.
Projected equalities explicitly select word substitution in the existing
shared machine walker, including inside signed observations; their shared
comparison storage does not turn them into exact-Integer substitutions.
The arena allocation proof and its reduced regression cover this distinction.
The rewrite consumer recognizes vacuous sign-cast equalities through same-format
shared observations, preserving the distinction from signed/unsigned exact
Integer equality. Its root-only check has cold DAG controls in both orientations.
Cold
DAGs at 16, 64 and 256 nodes have constant projection work and zero exports.
R7 is **closed**. Scaled indices use the shared carrier/read/scope summaries for
variable, capture, binder and current-memory dependency collection. Int32 offset
comparison uses retained operand views and the existing load authority; Int64
offset equality keeps its structural rule. Memory-blind fingerprints use one
encoding for native/shared operands and cached child hashes for shared syntax.
The cache is session-local, keyed by syntax identity, independent of facts,
registry changes and snapshot contents. Controls cover conversion/binder
payloads, registered reads, access widths, changed snapshots and native/shared
parity. Cold DAGs and growing fingerprint prefixes at 16, 64 and 256 nodes have
near-linear deterministic work and no exports.

R5 is **closed**. `index_bits` retains the rewritten machine carrier and
`rebuilt_index` preserves native constant, signed-widening and stride rules
without exporting shared arithmetic. Checked unsigned narrowing still requires
its original selected bound. Native/shared parity covers signed and unsigned
indices, negative/zero/positive strides and resolving versus written forms;
cold doubling DAGs at 16, 64 and 256 nodes stay shared with near-linear work.

R6 is **closed**. Mixed observations use retained syntax correspondence, and
unmatched shared arithmetic remains shared through selected read-equality
checking. Native stored-value evidence comes from the selected store itself;
the existing origin-chain rule accepts retained endpoints. Binder restrictions,
read widths and snapshot/source authority are unchanged. Controls cover opaque
mismatches in both directions, explicit source withdrawal, stored values,
unchanged origins and intervening writes. Multi-size cold mismatch controls
refuse without exporting or walking the shared arithmetic DAG. Existing
read-evidence tests still recheck authority after syntax-cache reuse.

#### Cleanup compiler audit — remaining conversions inventoried

Temporarily removing `SharedMachineIntegerTerm`'s `Deref<Target = MachineTerm>`
and `AsRef<MachineTerm>` implementations exposes implicit conversions that
text searches missed. The `fast-gate` test build reports both production and
test consumers; a diagnostic is not automatically a distinct checker gap.
The traits cannot yet be deleted. In particular:

- `PureFactContext::pointer_offset_congruence_evidence` now retains shared
  scaled indices through exact/direct bitvector evidence, additive cancellation,
  selected-source indexing and existing evidence checking. Offset linear forms
  retain shared leaves, including the residue test used to construct an offset
  equality. Surface certificate construction still has explicit native output
  getters; `scalar_evidence_class` still returns native terms to other
  consumers. `single_scaled_index_equal_to_constant` likewise still exposes a
  native index to the remaining order-path/condition-construction callers.
  Those compatibility boundaries are not closed by this increment. The native
  class API preserves syntax-sorted candidate order. Unsupported Integer
  equalities must be rejected before recording pointer-coordinate dependencies;
  they contribute no source edge and must not disable memory-query shortcuts.
- Contract certification now retains indices through byte bounds, additive
  endpoint construction, shallow binder-coordinate collection and selected
  read/cell equality. `contract_claims.rs` selects a read leaf directly. The
  checking-only simplifier memoizes shared DAG nodes; it does not change lowering.
- Difference-graph offset equality/residue, variable-chain index recognition,
  alignment factor inspection, store-gap roots and scope roots use operand views.
  Memory/binder walkers select retained leaves; memory provenance preserves
  first-occurrence candidate order. Proof-fact atom collection reuses its shared
  collector. Load-presence queries use syntax summaries, without enumerating
  growing free-variable sets.
- `PointerOffsetTerm::{for_each_scaled_value,any_scaled_value}` have no callers
  and are removed. The retained alternatives are `for_each_scaled_operand` and
  `any_scaled_operand`. `scaled_values` remains at native diagnostic/test
  boundaries; checker root queries use `scaled_operands`.
- Live at the contract-certification checkpoint (superseded below): native
  byte/element reconstruction in `reasoning/path_facts.rs`,
  exact-rebuild and selected-index order checks in `condition_reasoning/order_paths`,
  plus native consumers in `assumptions::{memory_reasoning,proposition_reasoning}`.
  `scalar_evidence_class` and `single_scaled_index_equal_to_constant` also retain
  their native outputs. These routes must migrate before removing the implicit
  traits; the contract increment does not close the entire cleanup audit.

This cleanup increment removes `map_scaled_values`, replacing it with a
shared-operand mapper. Equality-graph affine keys, offset interning, read-offset
classification and four-byte scaled-word source indexing retain their inputs.
Offset equality follows the existing shared-input policy: shared syntax and
read snapshots retain their identity; genuine native inputs take the legacy
comparison form before locking. No-export controls cover width/signedness,
source polarity/withdrawal, sibling contexts, snapshot identity and cold DAGs.
Validation: all 12 focused tests and the full gate passed (7,733 unit/API tests,
58 examples, 5,123 mdtests). The gate took 11m06s and emitted its existing
ten-minute budget warning; no limits changed.

The offset-evidence increment passed the full gate: 7,742 unit/API tests,
58 examples and 5,123 mdtests, including the unchanged duplicate-reference
refusal. The gate exited 0 in 14m18s (the environment restarted during the run,
but the process survived), with its existing ten-minute warning and no limit
changes. A separate combined scaling/focused run passed 1,415 tests before the
final dependency-bookkeeping fix; the final gate reran the scaling tests. Cold
success/refusal controls at 16, 64 and 256 operators require zero exports.

**Validated cleanup:** the contract-certification and retained walker
increment includes no-export, snapshot/source-withdrawal and DAG scaling
controls. Direct scalar-to-literal support is indexed on admission so a native
written equality and its shared operand query use the same source; this does
not permit transitive equality to substitute for a direct premise.

Validation: 50 focused arithmetic/loadability tests passed, followed by 72
focused difference-graph/contract tests after preserving the full-bit reading
of unsigned wide literals. The full `scripts/check.sh --no-fail-fast` gate
exited 0: 7,086 unit/API tests and all four fixture phases passed. It took
12m31s and emitted the ten-minute budget warning; no limits changed and no
nightly suite ran. The unrelated-block scaling test now creates a fresh
verification session per sample, retaining its exact work-equality assertion
instead of comparing one cold sample with two warmed samples.

The repeated production-library trait-removal audit reports 194 diagnostics
(previously 216); neither contract certification nor the difference graph
appears in it. This is a compiler-location inventory, not a count of remaining
checker routes: it also includes native outputs and diagnostics. The temporary
trait removal was restored byte-for-byte. The live exact-rebuild calls in
`condition_reasoning/order_paths.rs` and the Integer carrier scope call in
`spec.rs` are explicit next targets alongside the reconstruction services.

**Byte/element reconstruction increment:** `shared_byte_offset_from_pointer_offset`
and `shared_element_index_from_offset_with_facts` retain the index DAG while
building the same residues. The existing shared element builder is also the
implementation behind the native-output adapter. Full-width constants and
range evidence still control wide-to-word projection; low-word evidence,
unsupported widths and missing bounds do not suffice. The wide-equality
adjacency index now accepts retained query keys while preserving the native
syntax order of its source buckets.

Offset equality decision, offset-derived scalar path facts and exact-rebuild
checks consume those shared results. `single_scaled_index_equal_to_constant`
returns the retained index. Add/multiply exactness uses the existing shared
overflow query; accepting equal residues still requires exact rebuilds, while
unequal residues can refute equality without that premise. The obsolete native
signed-wide bound wrapper is removed. The difference-graph dispatcher routes
retained machine-order comparisons through its existing shared order checker;
this preserves full-width subtraction bounds and byte-array address proofs.
Native literal outputs bypass the general exporter, preserving the existing
per-cell store-work budget. Ambient-fact scaling tests use a fresh session per
size so cold and warm syntax caches are not compared. The fork/join sidecar
now proves its `range_filled` bridge by introducing the index and bounds,
instantiating the returned range fact, then rewriting the job fields. Those
simple steps pass on retained operands; the previous implicit closure exhausted
its unchanged work budget after the comparison representation changed. The C
program and claims are unchanged; no search fallback or budget increase was added.

At this checkpoint the native-output adapters remained live in memory resolution
and range checks, together with shallow scalar comparison/exact-constant queries
and `ExactElementDelta`'s native index field. The following increment migrates
those routes. The Integer carrier scope call in `spec.rs` remains separate work.

Validation: `scripts/check.sh --no-fail-fast` passed: 7,094 unit/API tests,
58 example projects, and 5,130 mdtests, including the scaling regressions.
Focused coverage includes missing/withdrawn full-width bounds, low-word-only
refusal, overflow refusal, and zero-export growing-DAG checks. The gate took
10m08s and emitted its ten-minute-budget warning; no limits were increased.
No nightly suite was run.

**Memory-resolution and range-index increment:**
`ExactElementDelta.index` and its single-index projection now retain shared int32
operands; the separate exact `i64` constant and the refusal to combine two
symbolic indices remain. Membership, exclusion, shifted-range coverage,
byte-gap checks, and exact rebuild comparisons consume operand views. The
literal-source index accepts retained input keys and preserves original premise
order. Affine index comparison visits a shared DAG once, propagating coefficients
without exporting or expanding repeated subexpressions.

Resource coordinate keys, selected range evidence, pointer-formation bounds,
and contract/loop range checks keep those operands. Range splitting retains
shared intermediate endpoints through its checks and exports only when creating
native `CMemoryRange` output bounds. Snapshot comparisons still enter the native
memory machinery only through selected read leaves. The unused native byte-offset
adapter and several obsolete checker wrappers are removed. Native pointer-index
output APIs still serve native resource/value producers and Surface tools; this
increment does not claim to remove every native carrier in the kernel.

Shared scalar equality admission retains its own replayable graph input rather
than reconstructing the equality through Integer observations. Read-equality
deltas preserve those inputs too. Selected comparisons reuse original native
bound sources; atomic read leaves enter their existing scalar comparison route.
Empty bounds indexes return immediately, and pointer-distinctness queries share
their existing resolution memo across the nested scalar checks.

The negative branch-interface fixture now explicitly rewrites its established
`k == 0` before combining the preserved-cell bounds. Its C, claims, and expected
definedness rejection are unchanged; the original omitted proof reached its
unchanged smart-search budget. No search fallback or limit increase was added.

Validation after rebasing onto current master: `scripts/check.sh --no-fail-fast`
passed: 7,109 unit/API tests, 58 example projects, and 5,146 mdtests. New tests cover exact-delta retention,
missing and withdrawn bounds, large constants and wrap refusals, zero-export
shared-DAG growth, and scalar-input replay with read-equality deltas. Existing
scaling tests compare fresh verification sessions at each size, retaining their
original limits. Focused fact-stability runs for the vector-prefix and negative
branch-interface fixtures passed with zero report entries. The rebased gate took
9m53s, within the ten-minute budget. No limits were increased and no nightly
suite was run.

#### Boundary audit after the memory/range increment

Repeating the production-library compiler audit with both implicit
`SharedMachineIntegerTerm` native traits disabled reports **178 diagnostics**
(previous checkpoint: 194). The temporary change was restored byte-for-byte.
This completes the inventory pass, **not** removal of every checker boundary.
The remaining locations divide into these concrete groups:

| Group | Remaining routes | Disposition |
| --- | --- | --- |
| Read/address checking | `memory_resolution` offset matching, exact-index materialization and selected read payloads; `memory_provenance` framed transport and exact-load normalization are closed below | Live checker migration; shared outer arithmetic does not eliminate native address children |
| Wide indices and shallow pointer checks | Wide access reconstruction, strided-region membership, offset transport and fold-read summaries are closed below; snapshot equivalence and `pointer_block_bounds` remain | Retain width, signedness and exactness rules while closing the remaining callers |
| Pointer fact/rewrite payloads | `arithmetic_special`, `equality_rewrite`, `fact_reasoning`, pointer-offset substitution and execution facts; snapshot-blind and alpha pointer-index fact keys are closed below | Mixed construction/checking boundaries; migrate expression children without changing pointer semantics |
| Resource and snapshot construction | quantified cells, memory-base roots, initialized-byte spelling, havoc identity, memory-load range collection | Mixed producer/checker boundaries, not merely printing |
| Native outputs and Surface tools | final `CValue`/`CMemoryRange` bounds, Surface synthesis/certificates, diagnostic renderers, planner segment indices | Explicit output or frontend/tool boundaries; remove only with their corresponding payload migration |

`scalar_evidence_class` is still a native syntax-sorted alias enumeration API.
Its callers include selected stored-value recovery, memory-base/root matching,
C operand simplification and a test-only reference inconsistency scan. It is
not a general shared arithmetic decision API, and must not be relabelled as
printer-only. `single_scaled_index_equal_to_constant`, in contrast, now returns
a retained index. `element_index_from_offset_with_facts` has only test callers;
production uses the shared helper. The conservative `integer_carrier_in_integer`
query already uses operand views and has no-export coverage; the distinct
`integer_carrier_in_pointer_offset` query remains in the compiler inventory.

At that checkpoint the residual traits could not yet be removed; the final
retained checker pass above removes them. Nested signed construction below
is independently guarded by zero-export and growth tests: its arithmetic and
obligations retain shared roots, with one final native value output at the
existing evaluator boundary. This does not declare step 1 or the complete
KernelTerm/SurfaceTerm split finished.

#### Retained pointer-index checks

Strided-region field checks pass operand views to their existing bound checker,
including the range-evidence caller; they no longer construct a native index
between selecting a stride and checking its bounds. Parameter partition roots,
open-side classification, and pointer-offset Integer carrier scope checks inspect
only the retained root. Pointer-offset transport uses the existing shared
transport checker. Mixed signed-word/unsigned-wide offset equality observes its
retained operands directly, and unsigned-wide index equality constructs a shared
comparison.

Fold-read offset summaries retain shared int32/int64 atoms and return a shared
scaled index. Their membership/exclusion checks use the existing selected exact
comparison source index, preserving strictness and missing-bound refusals. This
removes the native index storage from the summary itself; native interval bounds
remain input/output boundaries. Cold index DAGs at 16, 64 and 256 nodes have
constant summary-query work and zero exports. Focused controls cover stated and
missing bounds, both bounds of a strided field, and existing frame/refusal rules.

This increment closes those named consumers, not wide access reconstruction,
read-address payload normalization, snapshot-equivalence recursion, or the
remaining native pointer rewrite/fact-key families. The implicit native traits
remain until those callers migrate.

Validation: all 39 focused tests passed, then `scripts/check.sh --no-fail-fast`
exited 0 with 7,115 unit/API tests, 58 example projects and 5,149 mdtests. The
gate took 9m29s, within budget. Existing fold-read transport fixtures passed
before and after with zero fact-stability entries. No limits changed and no
nightly suite ran.

#### Shared wide access coordinates

Wide element-index reconstruction returns a retained operand. Its consumers in
range membership/separation, selected-source loadability, scalar writes and
translated range coverage check that operand directly. Full-width observer
equality inspects selected read leaves and existing exact equality neighbors;
it does not export an arithmetic prefix to find a load.

The former native wide-index helpers are removed. Existing signed extension,
nonnegative coordinate reconstruction, no-wrap guards, missing-bound refusals
and alias candidate order are preserved. Range rebasing retains the access
coordinate through its endpoint construction. `CMemoryRange` still stores native
endpoints. The `checked_native_range_endpoint` and `wide_range_bound_pair`
adapters also retain native checking callers (same-base coverage, alias-overlap
and pointer-formation checks, and split/merge decisions); those callers must migrate before these
adapters can be classified as output-only or removed.

Controls distinguish a full-width bound from a bound on the truncated low word.
Cold doubled index DAGs at 16, 64 and 256 levels reconstruct with constant query
work and zero exports. This closes the wide access reconstruction group above,
not read-address normalization, snapshot recursion, pointer rewrite/fact keys,
or generic native expression bridges.

The nested-rounding bound rule is shared by native and retained comparisons:
`(a - a % k) <= upper` needs a nonzero `k` and `a <= upper`. It follows
the dividend chain without exporting shared prefixes. Its old native form
incorrectly used a non-strict premise for a strict conclusion; the shared rule
refuses that inference. Controls cover the counterexample where rounding eight
twice by four still gives eight, missing/zero divisors, and growing shared
rounding chains. Literal coordinate construction and arithmetic use direct
paths so native-loadability queries have the same cost in cold and warm runs.

Validation: 88 focused tests passed. `scripts/check.sh --no-fail-fast` exited 0
in 9m17s: 7,125 unit/API tests, 58 example projects and 5,160 mdtests passed.
The two wide-range transport fixtures and the nested chunk-tail fixture passed
with zero fact-stability entries. The strictness counterexample and the missing
shared bound both failed before the common-rule fix and pass afterward.
No nightly suite ran.

#### Retained wide endpoint checks

The native endpoint/rebasing adapters listed above are removed.
`shared_wide_range_bounds` and `shared_rebased_wide_bounds` retain their
coordinates through same-base coverage, alias-overlap checks, pointer formation,
and split/merge decisions. Translated-window checking receives the selected base,
width and retained bounds directly; it does not need a temporary resource
containing exported endpoints.

Split and merge convert endpoints only when constructing their final
`CMemoryRange` outputs, preserving the original range carrier metadata. Native
endpoint storage and native normalization/fact keys remain separate boundaries;
this does not classify those consumers as migrated. Controls cover complete
versus truncated bounds, 64-bit split/merge outputs, and cold rebasing DAGs.

Validation: all 46 focused tests passed. `scripts/check.sh --no-fail-fast`
exited 0 in 9m14s: 7,128 unit/API tests, 58 example projects and 5,160 mdtests
passed. No nightly suite ran.

The production compiler audit after this increment reports 157 primary error
locations with the two implicit conversion traits disabled, versus 178 at the
previous checkpoint. These are caller locations, not distinct checker defects;
output, diagnostics and native payload construction also depend on the traits.
The traits were restored after the audit. After the cell-run and wide-offset closures below, remaining checker examples
include read-address/snapshot reasoning, pointer fact keys and native range
normalization.

#### Retained cell-run access indices

`RunAccess::Scaled` and `ScaledWide` retain the pointer's shared index instead
of materializing a native index in an intermediate access record. Exact-slot
lookup, store-window intervals and symbolic run loads use existing shared
constant/interval/comparison queries. They preserve exact 64-bit evidence,
missing-evidence refusal, slot holes, access widths and path exclusions.
The structural constant readers in offset atom collection, stride differences
and exact byte shifts also inspect retained operands.

Controls cover pinned and unknown slots, holes, signed 32-bit constant
interpretation, and cold repeated-child DAGs at 16, 64 and 256 levels without
machine exports. Native read-address normalization remains separate; the
stepped wide-offset equality route is closed below.

Validation: six focused tests passed. `scripts/check.sh --no-fail-fast` exited
0 in 9m24s: 7,132 unit/API tests, 58 examples and 5,160 mdtests passed. Both
wide-range transport fixtures passed with zero fact-stability entries. No
nightly suite ran.

#### Retained wide offset equality

The unsigned-64-bit constant and stepped-index routes in
`pointer_offsets_equal_for_memory_resolution` now retain their index operands.
The stepped route constructs its addition with `wide_index_binary` and uses
shared comparisons, preserving its complete-width no-wrap guard. Exact
constant evidence is read through `wide_constant_from_equalities_view`, with
the same equality directions and query order. A matching low word alone cannot
pin the full index.

Controls preserve the full high word, signed byte-offset refusals, misalignment,
missing no-wrap premises and wrapping increments. Cold shared DAGs and unrelated
fact populations exercise the same selected equality route without exporting
index trees. Read-address/snapshot reasoning, pointer fact keys and native range
normalization remain separate checker boundaries.

Validation: the full `scripts/check.sh --no-fail-fast` gate exited 0 in 9m01s:
7,135 unit/API tests, 58 examples and 5,160 mdtests passed. After rebasing onto
current master and reducing only the unrelated-fact test multiplier, all six
focused tests passed. The final growth test took 0.184s, retaining its three
DAG sizes and work/export assertions. No nightly suite ran.

#### Retained pointer-index memory evidence

`pointer_offsets_match_from_memory_derivations` uses the existing shared int32
value-equality and explicit memory-derivation queries for scaled indices.
`pointer_offset_equality_evidence` and its typed checker select read sources
through operand views instead of exporting shared arithmetic merely to inspect
its root. The native atomic evidence checker still enforces its read-root,
width and exact-snapshot requirements; this does not broaden its rule family.

Controls compare native/shared value answers, preserve changed-cell and width
refusals, and reject cold arithmetic DAGs at 16, 64 and 256 levels with constant
root-inspection work and zero exports. Framed pointer-offset transport and
exact-load normalization are closed below. The implicit traits and other live
checker migrations listed above remain open.

Validation: five focused tests passed. The full `scripts/check.sh --no-fail-fast`
gate exited 0 in 9m17s: 7,138 unit/API tests, 58 examples and 5,160 mdtests
passed. The subsequent rebase adds only an unrelated CLI change; no tested
kernel source changed. No nightly suite ran.

#### Explicit native address-walker boundaries

The four canonicalization/read-selection walkers explicitly borrow retained
native inputs after their shared-index guard. These eight call sites no longer
depend on implicit `Deref`. Shared indices retain their exact structure and
snapshots without entering the native walkers. This classifies existing native
input paths. Framed transport and exact-load normalization are closed below.

Validation: `scripts/check.sh --no-fail-fast` exited 0 with 7,142 unit/API tests
and the complete regular examples/mdtests. The cold run took 14m07s, including
3m48s compilation, and exceeded the ten-minute budget. A redundant standalone
documentation build was stopped after it competed with the fixture phase;
rendering and lint had completed. The unit phase took 276s versus 273s in the
previous gate. No limits changed and no nightly suite ran.

#### Retained pointer-formation bounds

Recorded-block formation checks retain scaled indices through signed/unsigned
wide comparisons and the signed extension of a 32-bit coordinate. Exact byte
coordinate reconstruction retains intermediate sums and products. Its signed
range requirements are ordinary Integer upper/lower bounds; unsigned indices
still need the full-width maximum-index guard before signed interpretation.
Opaque byte-offset variables and negative unsigned strides keep their refusals.
The coordinate constructors preserve native constant-reading and product
zero/one rules; they do not apply comparison-only simplifications to values.

A native/shared parity test exposed extension constant metadata that folded a
computed narrow operand where the native reader accepts only a literal of that
width. Shared metadata now preserves those literal requirements, including the
signed-to-unsigned wide extension. Retained native leaves supply their existing
constant reading once on introduction, including literal-conditioned native
conditionals; shared parents reuse the result. This is checking metadata, not a
change to structural lowering. Controls cover exact constructor shapes,
overflowing and full-width coordinates, missing bounds, read snapshots and
growing DAG prefixes.

The full gate exposed a common comparison-reader gap: removing an exact
extension could leave different observation formats and lose the original
common-format comparison. The reader now retains that written view when the
value reading cannot form a machine comparison. The existing mixed `int` /
`size_t` allocation-index fixture verifies unchanged, with zero fact-stability
differences; a unit regression covers separate bounds and missing premises.
Validation: `scripts/check.sh --no-fail-fast` passed in 9m49s with the
precompiled test binary: 7,150 unit/API tests, 58 example projects and 5,180
mdtests. The focused eight-test run includes deterministic 16/64/256-prefix
scaling and zero-export checks. No nightly run.

The distinct cumulative pointer-index producer and remaining compiler-audit
groups are still open. Framed transport and exact-load normalization are closed below.

#### Retained snapshot-equivalent pointer indices

The snapshot-equivalence route for 32-bit scaled indices now retains operand
views. Its shared syntax correspondence is cached separately from proof
authority: every selected read pair is checked under the current context.
The existing native rule remains the reference: exact syntax matches, and
changed read snapshots may be framed only through same-format 32-bit sums,
differences and products. Casts, other operations and wide arithmetic retain
exact-syntax matching but do not gain framing of changed reads. Variables do
not acquire registered-load semantics in this route.

The snapshot source index shares the native/shared operand fingerprint walker.
Its policy omits read addresses and snapshots only along those same permitted
paths, while the existing memory-blind fingerprint retains its own policy.
This also aligns the source-index shape with the existing unsigned 32-bit ring
comparison rule; previously the shape recognized only signed ring operations.
These fingerprints select candidates, never prove equality.

Validation: four focused tests pass, including native/shared and mixed parity,
source lookup in both orientations, withdrawn/missing premises, branch-context
authority and deterministic 16/64/256-prefix growth with zero exports.
`scripts/check.sh --no-fail-fast` passed with 7,154 unit/API tests, 58 example
projects and 5,180 mdtests. Its precompiled-binary run took 10m04s and emitted
the ten-minute budget warning, versus 9m49s for the preceding checkpoint;
no limits were changed and no nightly suite was run.

#### Remaining index-query adapters

Wide unsigned-index distinctness compares retained full-width operands,
including a constant byte displacement beside a scaled index. Mismatched or
nonpositive strides retain their previous refusal, and neither operand is
truncated to a low word. Exact scalar-constant substitution uses the existing
operand-view equality index and still requires the byte product to fit.
Shallow index equality calls the maintained graph through operand views.
Plain-origin classification reads only the root variable or literal and keeps
its existing accepted literal formats; computed constants remain nonplain.

The new controls exposed two shared-route gaps. Exact-constant source admission
now files written 32/64-bit machine observations as well as native comparisons,
retaining the original source condition and endpoint syntax. The contextual
wide-constant evaluator now memoizes completed shared misses by fact identity,
logical-read generation, node identity and evidence-capture mode. Positive
answers retain their existing source-evidence path; cycle/depth cuts mark the
incomplete-reasoning epoch and do not become completed negative entries.
The growing-prefix probe fell from 40,938 / 227,706 / 1,504,680 work units to
35,820 / 151,932 / 616,380 at 16 / 64 / 256 prefixes. Temporary call-site
profiling was removed from the source.

The compiler-assisted audit at `bef90e92c` temporarily disabled the implicit
`Deref`/`AsRef` tree conversions and found 120 primary locations, compared with
157 in the earlier endpoint audit. These include diagnostics, synthesis and
native output construction, not just checker dependencies. The traits were
restored after the audit; this count is a boundary inventory, not a claim that
all those sites are defects or that step 1 is closed.

Validation: all 11 focused tests pass, including deterministic growing-prefix
checks with and without evidence capture and zero tree exports.
`scripts/check.sh --no-fail-fast` passed with 7,158 unit/API tests, 58 example
projects and 5,180 mdtests in 9m41s with the binary precompiled. No limits
were changed and no nightly suite was run.

#### Exact-materialization index equality

The assumption-free offset comparison retains its indices while following only
root `int32` reads through exact stored cells. It does not normalize loads inside
arithmetic, reinterpret other read kinds, or resolve an unknown snapshot. Both
sides are materialized once; the existing bounded snapshot rule then receives
only selected native read leaves. Exact shared syntax correspondence reuses the
memoized operand matcher with framing disabled, preserving native literal and
operator distinctions without exporting either arithmetic DAG. This is also the
syntax-equality primitive needed by the remaining shared reconstruction work.

Validation: five focused tests pass, including native/shared/mixed parity,
root-only and kind refusals, separated/overlapping stores, havoc and cold-session
16/64/256-prefix scaling with zero exports. The full gate passed 7,161 unit/API
tests, 58 example projects and 5,180 mdtests. Its precompiled-binary run took
10m09s and emitted the ten-minute budget warning (preceding run: 9m41s). The
extra wall time was distributed across existing tests; the five focused tests
took 0.043s. This does not establish a cause for the variation. No limits were
changed and no nightly suite was run. Full exact-load normalization is closed
in the later increment below.

#### Framed pointer-index transport — closed

Framed transport retains shared scaled indices through memory updates. An
iterative, query-local walk visits each distinct arithmetic node once and
rebuilds shared children. Only selected native leaves enter the existing
memory-framing checks; no proof authority is cached across contexts or snapshots.
Native inputs still use the native walker. Raw 32-bit operators, wide constructor
constant readings, casts, stride simplification and the offset carrier convention
retain their existing rules. Opaque leaves retain their existing transport
refusals; this does not add a new memory equality rule.

Six focused tests pass, covering constructor parity, opaque constant readings,
registered load names, changed and unknown snapshots, overlapping stores, havoc,
and refusal paths. Cold repeated-child DAGs at 16, 64 and 256 nodes retain
near-linear deterministic work with zero machine-tree exports through the actual
pointer-offset entry point, for signed 32-bit and signed/unsigned wide indices.
The broader selected run passed 1,713 tests, including all nonignored scaling
tests, memory provenance, rewriting, transport API, documentation and search
boundaries, using the gate's existing 8 MiB test-thread stack. Formatting and
documentation rendering passed; advisory Vale lint was unavailable. The full
integration gate and nightly suite were not run locally; CI and the merge queue
run the full gate. The complete split remains open.

#### Exact-load normalization of pointer indices — closed

Exact-load normalization now uses the same iterative, query-local shared-index
walk as framed transport, with its own smart-constructor policy. It resolves
selected native load leaves through the existing snapshot/kind checks and
cycle guard, and retains shared arithmetic parents. Native inputs and opaque
selected leaves keep the native normalizer. Load authority never survives a
query or fact-context change. The narrow carrier, signed/unsigned wide reading,
stride reductions, and 32-bit smart folding (including sorted XOR cancellation)
retain their native rules. XOR orders selected atoms structurally without
exporting their shared arithmetic; rebuilding its normalized chain charges work
for the selected atoms and produced nodes.

Validation: all 1,721 selected tests passed on the rebased change, including all
nonignored scaling tests, memory provenance, equality/term rewriting, transport
API, documentation and search-boundary checks. The run used the existing 8 MiB
test-thread stack; compilation took 5m07s and tests took 116s (two slow notices).
The five new regressions cover native constructor parity, snapshot/kind/context
authority, and cold 16/64/256-node DAGs for unchanged arithmetic, resolved read
children and structurally ordered XOR atoms, with zero machine-tree exports.
Formatting and documentation rendering passed. The full integration gate and
nightly suite were not run locally; PR CI and the merge queue run the full gate.
The remaining compiler-audit inventory, producers, legacy families, and final
Surface/Kernel boundary remain open; this closes pointer-index normalization,
not the whole migration.

#### Retained pointer-index fact keys — closed

Snapshot-blind pointer-offset keys consume the retained machine operand view,
using the existing interned syntax keys instead of exporting an index tree.
Both narrow and wide scaled offsets preserve their stride and unsigned reading.
These keys still select candidates only: erasing a read snapshot never supplies
proof authority.

Alpha pointer-offset keys now retain the existing compact machine-key DAG,
including exact proposition identities and quantified candidate keys. Selected
native leaves keep their existing binder, load-kind, registry and snapshot rules.
Binders introduced inside an opaque machine leaf use leaf-local ordinals: a
repeated DAG child and repeated native syntax agree, while outer binders,
shadowing and free variables remain distinct. No load answer or binder-context
result is cached across queries.

Validation: all 1,796 selected tests passed, including every nonignored scaling
test, proof fact/key/reasoning tests, equality/term rewriting, transport API,
documentation and search-boundary checks. Seven new regressions cover native
syntax parity, repeated opaque binders, shadowing/free-variable distinctions,
stride/signedness, snapshot/kind authority, and actual fact-store hit/miss and
branch behavior. Cold 16/64/256-node DAGs and growing snapshot-key prefixes have
near-linear deterministic work with zero exports; lookup work stays bounded
beside 16/64/256 unrelated facts. Compilation took 1m36s and tests took 110s
(two slow notices), using the gate's existing 8 MiB test-thread stack.
Formatting and documentation rendering passed. The full integration gate and
nightly suite were not run locally; PR CI and the merge queue run the full gate.
The remaining checker inventory, producer migrations, legacy term families and
final common boundary remain open.

#### Classified boundaries and retained coverage

- `variable_collection::visit_machine_carrier_leaves`, ordinary shared Integer
  scope collectors, `assumptions::collect_shared_machine_memory_loads`, and
  `proof/facts/selected_atoms` select shared syntax/read/conversion leaves.
  Their native fallback requires an actually native operand. This classification
  includes the pointer-index edges closed in R7. Existing cold-DAG, growing-prefix,
  binder and registry tests remain applicable.
- `proof/signed_arithmetic/atom_keys` works on shared syntax and retains its
  explicit conversion/opaque refusals. `proof/integer_arithmetic` keeps machine
  observations as shared atoms; no new boxed checker dependency was found in
  these audited adapters.
- Shared `IntegerTerm::RangeFold` bodies and endpoints retain their shared
  walkers on the supported path. Opaque source and replacement handling is covered by the closed R1/R2 paths,
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

The initial audit ran 59 syntax/rewrite controls and 13 registry/dependency
controls; the later R1–R7 closure evidence is recorded above. R5/R6 validation
passed 1,404 scaling/focused tests and the full gate: 7,729 unit/API tests,
58 example projects and 5,123 mdtests. The gate exited successfully in 10m48s
with its existing ten-minute budget warning; no limits were changed.

**Delivery order:** finish the live checker routes found by the cleanup audit
and remove the implicit adapters. Producer increments may proceed when their
own shared construction/obligation paths have zero-export and growth controls;
this does not close unrelated pointer/address checker routes. Keep
one coherent PR open at a time. R1/R2 reuse the exact native-leaf boundary
introduced for tagged addresses; no opaque term-family redesign was required.

### 2. Finish expression producers

`kernel/spec/shared_machine.rs` constructs complete same-format trees of signed
and unsigned addition, subtraction and multiplication. One iterative selection
pass rejects deferred/mixed trees before imports; one construction pass retains
shared children and signed range obligations in left-to-right evaluation order.
Literal folding remains evaluator-only. The single-operation signed module is
removed. Available machine leaves use the existing retained-machine boundary,
so opaque Boolean, pure-function and binder payloads preserve their observation
identity beneath shared arithmetic. The general term importer is not a substitute
for that machine boundary. `SpecExpressionPath` now retains these results as
`SpecValue::Shared`; native inputs and unmigrated sorts use its explicit native
variant, with conversion only at consumers that still require native payloads.

Validation: the final `scripts/check.sh --no-fail-fast` exited 0: 7,111 unit/API
tests, 58 example projects and 5,146 mdtests passed. This includes cold nested
production at 16, 64 and 256 operations, zero intermediate exports, obligation
order, retained inner overflow, held-resource metadata, opaque machine leaves,
and the unchanged Rust integer-language example. Signed-fixture fact-stability
runs passed before and after with zero entries. The full gate took 13m41s,
including a 3m45s rebuild, and emitted its ten-minute-budget warning. No existing
limits were raised and no nightly suite ran.

- [x] Enable nested signed construction with shared obligation operands. This
  producer's zero-export contract is separate from the residual address/pointer
  boundaries inventoried above.
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

#### Live producer inventory after checker closure

The next producer/common-raising increment retains division, remainder and
shift domains, gives Integer conditionals common children, and raises migrated
machine/Boolean children directly. Indexed current-local naming preserves
existing loop proofs and diagnostics without exporting shared arithmetic.
Its full gate passed 7,205 unit/integration tests and all four fixture harnesses
in 12m55s, over the ten-minute target; no limits were changed. The production
build passed. Full regular-corpus fact-stability runs before and after both
passed with zero fact-dependent lowerings. Native/shared parity, source-drop
round trips, local-index collision checks and deterministic 16/64/256-node
zero-export regressions cover the new boundaries. Steps 2–4 remain open.

| Producer | Representation boundary still to close |
| --- | --- |
| `spec/shared_machine::prepare` | Same-format available 32/64-bit arithmetic, including division/remainder and shifts, retains common children and debts through `SpecExpressionPath::value`. |
| `spec::evaluate_spec_expression_dispatch` | Deferred same-format 32/64-bit arithmetic, including shifts, and scoped requirement handoffs retain results and debts. Opaque/read operands retain shared surrounding arithmetic through domain construction and Integer observations; a session-local memo maps opaque leaves to the existing numeric observation identity without changing exact producer payloads. Same-format 32/64-bit scalar comparisons retain shared operands. Literal-right add chains evaluate iteratively with retained prefixes, including deferred bases. Same-format casts retain the existing result and debts. Specification let bindings retain shared machine values through a persistent lexical map and iterative binding evaluation, including nested values; native C expressions materialize only the lexical names they explicitly read. Symbolic machine conditional joins retain typed guards and shared arms through checking, observation identity, pointer-index transport and Surface spelling. Mixed/narrow/wide operations, representation-changing casts, folds, pure-call arguments, pointer indices and C execution/API outputs still have explicit native boundaries. |
| `eval/operators` and `eval/operators/spec_arithmetic` | C execution, Rust shifts, conversions, bitwise operations and wide operations construct native `CExpressionOutcome::Value` payloads. Runtime-error branches and logical specification debts have distinct rules. |
| `ProofObligation::verification_condition` | Observation canonicalization now retains shared comparisons instead of exporting their prefixes, preserving polarity and native/shared checking equivalence. |


Result-carrier validation: all 1,442 scaling tests passed; the combined gate's
unit phase passed 7,212 tests. Its fixture phase exposed two deferred-shift
domain regressions (PCG and unsigned wide narrowing). The compatibility
boundaries above preserve the old domain shapes: all 58 examples passed their
rerun, all 18 shared-producer regressions passed, and the final production
fact-stability run passed all 5,188 mdtests with zero differences (the baseline
also had zero). The final boundary fixes were checked by these targeted and
corpus reruns; the combined gate was not rerun afterward. Steps 2–4 remain open.

The deferred-domain/comparison increment removes the opaque-domain and deferred
shift compatibility exclusions. Native observation inputs and shared producers
now agree on numeric identity even after the producer is dropped. Signed claim
recognition, certificate term selection and typed comparison spelling read the
retained comparison view. The bounded tagged-address certificate evaluator
borrows shared operands directly, retaining its payload limits, alignment
requirements, relation-cycle refusal and tag rules. Its explicit source terms
and alignment evidence remain the only inputs; no ambient proof search is added.
Signed interval planning bounds and exports selected operands once for the
existing public certificate payload; its affine evidence matcher reads shared
claims directly. Shared cast raising keeps Surface operands, including snapshot
selectors, instead of forcing them through C fragments. Opaque conditional
operands retain their interval rules and Surface conditional spelling. Resource
body requirement matching recognizes retained comparison directions and exact
stored reads. Guarded-consequent indexing, spelling and rewrite selection read
shared comparisons, preserving explicit guard discharge and indexed candidate
selection. Native/shared comparison transport uses the same selected operand
rules. Proper-conjunct extraction keys native and retained observations alike,
without admitting an independently held fact as a conjunction projection.
Cited-condition rewriting visits opaque payloads and folds resolved conditional
arithmetic; wide word equality retains the signed interpretation of high-bit
literals. Difference-graph interval queries borrow retained opaque leaves and
preserve their native branch rules without exporting surrounding arithmetic.
Theorem requirement selection and checking bridge listed equality and disequality
premises as well as order claims. Goal completion checks the selected theorem's
conclusions through the same bridge. General rewrite/transport candidate matching
keeps its existing order-only admission. Resource match/unfold consumers use the
producer's paired clause records directly instead of rechecking them against a
differently represented fact store.
The public signed certificate's selected term payload is still native, as are
the remaining producer families listed above. Steps 2–4 remain open.

Validation after integrating upstream through #2607: all 1,453 scaling tests
passed. The gate's unit/API phase passed 7,242 of 7,243 tests; the one expansion
failure exposed early completion of a mirrored order goal. Restricting the new
completion bridge to equality fixed it, and all 106 selected tests passed on
rerun, including the complete expansion suite and mutex-parity fixtures. All
58 examples passed afterward. The production build and all 5,210 regular
fixtures passed, with zero fact-stability differences (305 seconds). The two
new upstream store-search diagnostic fixtures also passed with retained typed
spellings, including the heap variant outside the regular corpus. The combined
gate was not rerun after the fix; the nightly suite was not run.

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

#### Live payload and common-boundary inventory

| Family | Current storage / bridge and disposition |
| --- | --- |
| Mathematical Integer | `SharedIntegerNode` retains `IntegerTerm` plus a cached `KernelTerm`. Arithmetic, calls and conditionals have common children. Folds and algebraic matches still need typed common children and binder metadata. Remove the parallel native node storage after its readers migrate. |
| Machine values | `MachineTerm` and native `CValue` payloads remain producer/result carriers. Shared arithmetic, casts, machine conditionals and read descriptors are common nodes; fold, application, algebraic-match, pointer-address and floating payloads still use generic bridges on some routes. |
| Logical Bool | Comparisons, calls, equality and conditionals have common nodes. `LegacyBool` still carries pointer/offset/complete-pointer comparisons, algebraic equality, overflow and floating conditions, and Boolean loads. |
| Complete pointers and read addresses | Keep address, designation, opaque extent, qualifiers, subobject extent and access/evidence metadata. Expression children must migrate; snapshot, allocation and execution-event identities may remain semantic atoms. A wrapper around the existing complete pointer tree is not closure. |
| Algebraic values and array references | `KernelTermImport::argument` still uses the generic legacy argument boundary. Constructors, matches and scalar children need typed common nodes; array-reference snapshot identity remains an atom. |
| Raising/lowering | `raise_kernel_term` visits common arithmetic, casts, observations, machine/Integer conditionals and Boolean children directly. Shared arithmetic uses the existing local-name index before expanding children; it preserves current-local spelling without exporting the query or scanning unrelated locals. Legacy payload dispatch, native fact/goal synthesis, certificate-only lowering and the general evaluator-backed lowering path remain distinct boundaries until consolidated. |

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

The R1–R7 reproductions above are closed, but the compiler-assisted cleanup
audit found additional live routes. Finish those checker migrations and remove
the implicit adapters before proceeding through steps 2–4. Do not resume the
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
