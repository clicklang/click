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

1. **Call-side fragment composition: removal experiment needs proof repairs.**
   The local experiment removes the automatic coalescing prepass from
   `plan_stable_view_transfer_with_protocol_effect`. The fixed-gap regression
   `call_fragment_composition_stops_at_a_fixed_gap` now passes: repeated
   complete-call work is 28 at 4/16/64/256 rejected fragments, versus
   315/711/2295/8631 before removal. Persistent-map visits are 229/319/443/567,
   versus 5722/22006/105598/524218. Its range indices denote four-byte cells:
   `[0..1]` is held, cell 1 is missing, and extras start at cell 100. Complete
   ownership still supplies the view; disconnected observations do not.

   Validation of the un-repaired experiment: all ordinary example projects
   pass; 1360 of 1361 scaling/loan tests pass, with
   `mixed_width_view_backing_joins_only_its_own_pieces` failing as expected.
   5020 of 5027 Markdown fixtures pass. Failures are:
   - `a_kept_view_of_mixed_width_owned_fields_is_lent_until_released`
   - `writing_a_field_while_its_kept_view_is_lent_is_refused`
   - `cpp_class_const_method_keeps_fields`
   - `cpp_class_const_method_keeps_fields_rejects_overclaim`
   - `cpp_class_const_reference_keeps_fields`
   - `cpp_class_subclass_local_object_packs_itself`
   - `cpp_polymorphic_base_construction`

   These fail to supply a whole-object stable view from separate owned pieces.
   The two negative fixtures now refuse prematurely, not at their intended
   safety checks. Keep those checks and the original C/contracts intact.

   Explicit proof experiment: declaring `resource Whole(p: struct S*) {
   owns *p; }`, then `fold(Whole(p)); unfold(Whole(p));` before `lend(p)`
   proves the mixed-width struct fixture. It is not yet a satisfactory repair:
   fold's ownership consumption uses `without_fact_incrementally`, whose
   fallback also collects and normalizes the candidate frontier. The temporary
   proof edit was restored. This establishes expressibility, not fast checking.

   Next design/build checkpoint: investigate reusing the existing indexed
   `reserve_owned_memory_fragments_with_origins` construction for explicit
   owned composition. It consumes successive selected pieces and stops at a
   gap; verify mixed-width coverage, provenance, refusal behavior, and complete
   fold cost before adopting it. Do not introduce a new tactic or separation
   axiom merely because the implicit prepass was removed. Do not relocate
   candidate search into proof repairs. C++ object packing needs concrete
   repairs as well; successful struct folding alone does not establish them.

   `functions.rs` also calls `with_coalesced_owned_memory` in
   `unsupplied_local`, to classify implicit local-storage authority. That use
   remains unchanged in this experiment. Its removal must preserve authority
   classification; deleting a negative guard blindly could grant authority.
   The removal is a local checkpoint, not ready for publication.

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
