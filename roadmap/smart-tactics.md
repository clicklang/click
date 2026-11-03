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

1. **Parent loan-binding selection.**
   `view_occurrences_for_fact` in `src/kernel/primitives/resource_algebra.rs`
   enumerates matching observations; the call planner in `src/kernel/loans.rs`
   collects them and searches for a live parent loan binding. This happens
   both while deciding whether to coalesce a view and while selecting its
   backing. A crowded bucket of unbound observations must not cost a scan.

   `split_owner_reconciliation_ignores_duplicate_observations` in
   `src/scaling_tests/kernel/loans/tests.rs` holds a call fixed: consume
   `[0..4]` and borrow `[6..8]` from one `[0..8]` owner. At 4/16/64/256 duplicate
   observations, identity reconciliation itself is flat, but the test also
   reports growing complete-call persistent-map work. Ordinary work counters
   miss rejected-view traversal, so retain the persistent-work measurement.
   The complete-call curve is diagnostic, not yet a flatness assertion.

   The local red test
   `parent_loan_binding_selection_ignores_unbound_observations` in the same
   file measures the selection expression and the actual call, with index
   preparation outside both. It repeats queries at 4/16/64/256 observations
   for early and late bindings, two usable shares, no binding, an ordinary
   owner beside unbound observations, and a stale binding. Success, refusal,
   and branch-isolation controls pass before the scaling assertion fails.
   With an early binding, repeated selection map visits are
   195/399/1467/6855; complete-call visits are 1879/2291/4431/15211. No-binding
   selection is almost identical: 194/398/1466/6854. Ordinary selection work
   stays at 35, so it does not expose this traversal. The test is explicitly
   ignored while red; run its exact name with `--run-ignored all --no-capture`.

   Design checkpoint: skip discovery when the parent-binding map is empty;
   for nonempty maps, nominate a bound occurrence from an index maintained
   with binding updates, rather than collecting all matching observations.
   Start with exact requested views, including the two-usable-shares case.
   Keep the existing live-occurrence, live-loan, and actual-view/binding
   coverage checks. A stale or unsuitable nominee must not start another
   search. The coalescing prepass must likewise stop enumerating observations
   just to test whether one exists. Subrange and checked-offset-alias cases
   need bounded selection too: retain `nested_view_reborrow_accepts_checked_offset_alias_and_preserves_authority`
   and the wider-child refusal as acceptance controls, without an iterator
   fallback. No new separation axiom or surface tactic is indicated.
   Discuss this design before implementation; keep it separate from split
   origins and do not reconstruct bindings from context or ledger history.

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
