# Smart tactics: fast checking and enforceable search boundaries

Priority: P1.

Soundness: not soundness. This item concerns checking cost, separation of
search from checking, and accurate performance diagnostics. No false
acceptance is known. Removing automatic reasoning may lose proofs; explicit
proof repairs must preserve the original C and claims.

## Scope and invariant

Track remaining work only. The tactic model is documented in
[Smart and simple tactics](../docs/concepts/smart-and-simple-tactics.md);
the cost contract is in
[Verifier design](../docs/internals/verifier-design.md) and
[Verification efficiency](../docs/internals/verification-efficiency.md).

Checking must scale with explicit input, indexed access and the state delta.
Search may choose premises and try alternatives only under a deterministic
budget, with an explicit form that expansion can emit. Checking may decline
or emit an obligation rather than recover a proof through a hidden search.
Preserving all existing automatic proof coverage is not a requirement.

The work below was authorized on 2026-10-27. Suspected walks are investigation
targets, not claims of measured regressions. Establish a deterministic curve
before choosing each performance fix. Do not raise limits to hide a defect.

## First increment: measure call normalization

Reproduce the current cost of `add_normalized_verified_ensure_facts`
(`src/kernel/functions.rs`) through constant normalization in
`src/kernel/assumptions/condition_reasoning/decision.rs`.

The historical `authority_pool_control_two_members.md` measurement attributed
about 119,000 of 140,820 units in the second `give_back` call to snapshot
bridging. That is not a current baseline: the fixture subsequently failed in
`checkout`, before the measured call. Reproduce on current master, or reduce
the path below that unrelated proof failure.

Concrete candidate: `constant_class_resolution` calls
`scalar_bridgeable_loads`, which builds pairs of unknown-class loads and
settled loads indexed by memory-blind address, then calls `loads_bridge` on
the pairs. The unregistered-term path also visits settled loads at an address.
The current index does not itself establish a bound on bucket size, pair
construction, or repeated memory walks.

Current reproduction (2026-10-27, base `0b4123b8e`):
`constant_bridge_candidate_pairs_scale_with_selected_input` in
`src/scaling_tests/kernel/equality_graph/int32_tests.rs` constructs N reads
at call-havoc snapshots equal to one unknown value, followed by N reads at
later call-havoc snapshots equal to distinct constants. Each havoc may write
the queried cell. Setup is outside the measurement; one constant query
correctly returns unknown in every case.

| N per group | Candidate pairs | Construction work units | Full query work units |
| ---: | ---: | ---: | ---: |
| 4 | 16 | 5 | 1,521 |
| 8 | 64 | 9 | 6,081 |
| 16 | 256 | 17 | 24,321 |
| 32 | 1,024 | 33 | 97,281 |

The regression's near-linear candidate-growth assertion fails. The full query
cost is `95*N*N + 1` in these samples. Construction allocates N squared pairs
but charges only N + 1 units. This is a reduced kernel-query reproduction,
not a remeasurement of the historical full call fixture. A direct-store
prototype did not reproduce the issue: read-over-write normalization removed
the candidates. The existing positive control
`constant_normalization_bridges_a_load_across_a_call` passes in both modes
below: its name does not establish reliance on this particular fallback.
No behavior fix has been chosen; the failing regression is retained on the
investigation branch for discussion, not submitted to the merge queue.

Dependency experiment (same base, no proof edits): temporarily disable both
load-bridge loops in `constant_class_resolution`, keeping exact class lookup,
conditional resolution and arithmetic folding. The synthetic query then costs
one unit at every size. All 57 regular example projects (including `arena`)
and 4,851 enabled Markdown proofs pass. Of 6,325 enabled non-gate unit tests,
6,324 pass; the sole failure is the source-policy test rejecting the temporary
environment switch. After removing the probe from source, that policy test
passes too. The existing positive bridge test and the targeted nightly
`counter_call_chain_ensure_lowering_stays_flat_per_call` both pass with the
fallback disabled. No regular-suite proof dependency was observed.

`authority_pool_control_two_members.md` fails at the same `checkout` arithmetic
certificate with bridging enabled and disabled; it remains an unrelated
baseline failure and does not measure reliance in its later calls. The full
nightly suite was not run, including the four nightly-only example projects
(`rbtree-insert`, `rbtree-erase`, `rbtree-augmented`, `string-get-size`). This
experiment establishes regular-corpus compatibility, not universal
completeness or a timing speedup. The production source is restored.

Remaining regression coverage before a chosen fix:

- Grow unrelated facts, same-address snapshots, and members of the queried
  equality class independently, at several sizes; cover hits and misses.
- Measure candidate construction and bridge work, including allocation and
  iteration before a decision starts charging. A counter that omits the
  expensive loop is not evidence of good scaling.
- Measure repeated calls/queries as well as one query, to expose repeated
  history walks and quadratic total work.
- Retain `counter_call_chain_ensure_lowering_stays_flat_per_call` as an
  existing control; it is not coverage of all same-address candidate shapes.

Choose the smallest fix after measuring: retain cheap producer-established
relations, use a justified index, or decline the automatic inference and
make the necessary premise explicit. Do not add a second history walker.
Coordinate memory implementation with
[fact-aware-frame-walks.md](fact-aware-frame-walks.md) and pointer-read naming
with [unspellable-facts.md](unspellable-facts.md); those items own their
respective migrations. This item owns the measured cost and enforcement
requirements, not duplicate migrations.

## Fast-part scans

The remaining audit targets include indexed walks as well as full scans:

- Constant-normalization candidate pairs and snapshot bridges above.
- Atom-condition open-fact buckets and alias traversal, including large
  related buckets and repeated failed queries.
- Resource candidate lookup with open/loaded/symbolic bases and retained
  whole-block fallback, where still present. Confirm current callers before
  carrying forward an old census claim.
- Repeated memory-history queries, coordinated with the frame-walk item.

For each confirmed defect, retain its small reproduction and deterministic
curve in `src/scaling_tests/`, then remove it from this list when fixed.
Large explicit proofs and legitimately enumerated paths still cost work;
expansion is not expected to eliminate that semantic output.

## Enforce the checking/search API boundary

Consolidate heuristic planning behind a clearly named search module and
restrict the operations it can expose. A directory move alone is insufficient.

- Search may invoke checked operations; checked operations must not invoke
  planners or acquire the authority to enumerate ambient facts for search.
- Require a search capability, with restricted construction, for ambient
  enumeration. Audit current `scan_for_search` callers and broad fact-view
  APIs; a method name or comment alone does not enforce the boundary.
- Represent explicitly supplied premises separately from ambient context so
  checking can traverse the selected input without gaining ambient iteration.
- Audit upkeep/rebuild APIs too: renaming a query scan as upkeep or explicit
  input must not evade the restriction. Whole-context maintenance cannot run
  repeatedly on a small step's hot path.
- Preserve indexed checking and structural traversals of explicit input.
  Do not require a search capability just to check a large certificate.

Intended regression: a compile-time boundary test or dependency check rejects
an attempted planner call or ambient search enumeration from checking code.
Positive tests retain legal explicit-premise checking and planner access.
Introduce the boundary incrementally without claiming that a token proves
complexity: ordinary vectors and oversized indexed buckets still need scaling
coverage.

## Enforce growth and expansion regressions

- Checking changes name each index/key and add deterministic growth coverage
  for unrelated state, relevant chains/buckets, misses, and repeated steps
  where applicable. Keep small representative tests in the gate; reserve
  larger measurements for focused/nightly runs.
- Charge visited candidates and relevant state work, not just successful
  lookups. Test instrumentation coverage when a formerly uncharged loop is
  involved.
- Search changes test that successful expansion verifies with the selected
  search disabled or instrumented to reject re-entry. Explicit output must
  not silently invoke another helper to rediscover the same choice.
- Keep semantic negative controls: aliasing writes, snapshot changes, type
  and width mismatches, and withdrawn assumptions must remain refusals where
  applicable. Do not preserve speed by weakening the claim.

Update the design skill and contributor guidance alongside enforceable checks;
policy text alone is not the acceptance criterion.

## Attribute expensive checking inside search

Audit existing per-class budgets and exclusive-time attribution before adding
new reporting. A checker called by `solve` must not hide its cost or its
failure under a SMART label merely because its caller searches.

Intended regressions use synthetic deterministic work, not sleeps:

- A single expensive checked operation nested under `solve` or an elided
  argument search is attributed to checking and diagnosed as an engine
  performance defect, naming the operation and its enclosing source site.
- Many individually cheap checked alternatives exhaust the search budget
  and recommend intermediate steps or explicit arguments.
- A completed expensive search can recommend expansion; a failed search has
  no successful result to expand.
- A whole-run exhaustion without one offending operation reports aggregate
  work; a wall-clock containment timeout reports interruption and the active
  operation, not a machine-load-dependent proof verdict.
- Costs reconcile without double-counting nested operations; search budgets
  still bound total exploration, including the checks it invokes.

Checking allowances must account for explicit input/state delta where needed;
a fixed wall-time threshold alone cannot distinguish a large legal operation
from a pathological walk. Test normal verification and profile consistently.

## Acceptance

- Each confirmed expensive checking path above has a measured fix or an
  explicit, bounded refusal with proof repairs; unmeasured candidates are
  resolved by measurement rather than silently declared fast.
- Search-only ambient enumeration and planner dependencies are mechanically
  restricted, with negative boundary tests.
- Relevant deterministic scaling and expansion-without-search regressions
  run in the appropriate gate and catch the failure they claim to prevent.
- Nested checking failures and search exhaustion receive distinct actionable
  reports, including work outside written tactic sites.
- Documentation describes the enforced boundary and its remaining limits.
  Delete this item when these criteria land; do not accumulate a completion
  history here.
