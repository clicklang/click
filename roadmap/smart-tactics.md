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

## Fast-part scans

The remaining audit targets include indexed walks as well as full scans:

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
