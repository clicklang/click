# Smart tactics: fast checking and enforceable search boundaries

Priority: P1.

This item concerns checking cost and separation of search from checking.
Removing a walk must preserve safety refusals: an inconclusive bounded query
is not evidence of preservation. Proof repairs must preserve the original C
and claims; preserving all automatic proof coverage is not a requirement.

## Scope

Track remaining work only. The contract is in
[Verifier design](../docs/internals/verifier-design.md),
[Verification efficiency](../docs/internals/verification-efficiency.md), and
[Smart and simple tactics](../docs/concepts/smart-and-simple-tactics.md).

Fast checking must scale with explicit input, indexed access and the state
delta. Expansion cannot remove its cost. The implicit closer is separate from
`step()` checking: budgeted, expandable premise selection in `solve` or the
closer is legitimate search, even when a bare step invokes that closer.

Arithmetic premise collectors such as `signed_constant_bound_facts` are not
fast-checking defects merely because they enumerate candidates. Their current
ambient callers select proofs in the smart closer/planner; checking a written
certificate may traverse its explicitly cited premises. Add a collector to the
work below only with a demonstrated checking caller or an expansion/budget defect.

## Remaining checking walks

These are concrete checking call paths. Code inspection establishes the walks;
measure their growth before choosing fixes. Existing flat tests with unrelated
facts do not establish flat cost as the queried class or bucket grows.

1. **Call-side fragment composition: red test and design checkpoint.**
   The loan planner's coalescing prepass calls
   `ResourceContext::with_coalesced_owned_memory` when no nominated owner or
   bound view supplies a memory requirement. It materializes the candidate
   frontier and normalizes it before discovering missing coverage.

   `call_fragment_composition_stops_at_a_fixed_gap` in
   `src/scaling_tests/kernel/loans/tests.rs` holds a view request for
   `buffer[0..1024]` fixed, with ownership of `[0..1]` and a gap at byte 1.
   Add 4/16/64/256 disjoint one-byte owned fragments starting at byte 100;
   none can fill that gap. Index preparation is outside measurement. Repeated
   coalescing work is 259/655/2239/8575; complete-call work is
   315/711/2295/8631, with 5722/22006/105598/524218 persistent-map visits.
   Each query correctly refuses without changing the source branch. The same
   test checks successful two-piece composition beside out-of-range owners,
   and refusal beside observation-only additions: their ordinary work stays
   flat, with only indexing growth in map work. All semantic controls run
   before the intended scaling assertion fails. The red test is ignored;
   run its exact name with `--run-ignored all --no-capture`.

   Proposed next experiment, for design review: remove the implicit coalescing
   prepass and identify actual proof dependencies. Try explicit composition
   for affected proofs, preserving C, contracts, ownership and loan refusals.
   Check that a repair selects its pieces rather than merely moving this scan
   to another tactic. Do not add a replacement search or a new primitive before
   reducing a concrete missing explicit step. The existing indexed fragment
   reservation route is a separate possible implementation to assess, not
   evidence that the automatic coalescing prepass is necessary.

   Owned requirement reservation also uses
   `reserve_owned_memory_fragments_with_origins` and the unselected
   `without_fact_incrementally_with_origins` route; this reproduction isolates
   the viewed-requirement prepass, not every composition path.

2. **Loop retained-frame candidates: remaining measurement boundary.**
   With an explicit view interface, `with_loop_frame_resources` visits the
   owned-memory index to retain declared scalar owners. It still examines
   heap-owned memory that the scalar predicate rejects. Without an explicit
   view interface, it enumerates the withheld frame to build retained views.

   Measure a fixed retained scalar frame beside growing rejected owned-memory
   candidates, including the complete body constructor and persistent-map
   work. Distinguish rejected candidates from output-sized frame construction.
   The observation/binding-carryover regression does not establish bounded cost
   for arbitrary owned frames. Frame visits must remain charged. Establish a
   red test and discuss the design before changing this selection.

Memory-history traversal is also tracked in
[Fact-aware frame walks](fact-aware-frame-walks.md).

For subsequent history removals, follow
[Fact-aware frame walks](fact-aware-frame-walks.md). Retain repeated-query,
adjacent-state, exact, explicit-composition, cold-refusal and partial-overwrite
controls in `src/scaling_tests/kernel/tests/memory_scaling_tests.rs`.

Repair affected proofs with explicit separation and transport certificates,
preserving C and contracts. Structural read equality needs positive evidence;
an undecided bounded query cannot authorize equality. Retain freed-pointee,
partial-overwrite, provenance, and width refusals in every removal.

Keep certificate equalities at the footprint's exact entry/exit snapshots;
connect later observations with separate explicit normalization or preservation
steps. Use recorded typed reads, without reconstruction or history discovery.
Finish footprint producer integration for joined branches and loops only with
a concrete proof need; support whole-region separation by explicit composition,
not a transition scan. Extend observations beyond memory only with an explicit
primitive design and a concrete use.

Migrate implicit framing tests to explicit proofs, retaining aliasing and
overlap controls.
This item does not require a general audit of all history upkeep, diagnostics,
or verifier code before closure.

## Acceptance for each target

- Establish deterministic work curves at several sizes through a fast-checking
  caller. Charge candidate visits, include repeated queries and misses, and
  separate explicit input/state-delta growth from ambient candidate growth.
- Replace implicit enumeration with indexed summaries/selection, or decline
  with an obligation that explicit proof steps can discharge. Search for an
  alternative belongs in budgeted planning with an expandable explicit form.
- Retain semantic controls for widths, snapshots, aliasing writes and branch
  isolation. Branches extend persistent contexts; do not withdraw facts to
  backtrack. Preserve C and claims in proof repairs.
- Add growth regressions and the relevant checking/search API boundary guard.
  When search is involved, verify expansion without re-entering that search.
- Attribute excessive checking to checking even inside `solve`; legitimate
  search exhaustion remains a search diagnostic. Extend `CheckingWorkScope`
  where a migrated checker needs coverage, using explicit input/output measures,
  and preserve the existing nested-budget and accounting regressions.
- Update the design guidance alongside the enforced boundary. Remove each
  target when resolved by measurement and a fix or justified classification.

These are acceptance criteria for the named targets, not an open-ended list of
new audits. Add another blocker only with a concrete checking call path or
reproduction. Close this item once its named targets are resolved and their
regressions and boundary checks land; do not accumulate a completion history.
