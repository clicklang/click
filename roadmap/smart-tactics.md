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

1. **Remaining fragment-selection routes.**
   `without_fact_incrementally_impl` still enumerates candidates for requests
   outside constant, 32-bit-indexed, unit-owned memory. `satisfies_fact` also
   retains a normalization-based memory-supplier fallback. Isolate real checking
   callers and red scaling curves before changing these remaining routes.
   Distinguish the relevant pieces consumed by explicit composition from
   rejected candidates and speculative searches. Preserve symbolic/wide range
   carriers, split origins, ownership refusals and branch isolation. Incremental
   ownership-validity checking still enumerates related candidates when the
   constant same-base neighbor index cannot represent the block (for example,
   symbolic bounds or native byte coordinates beyond its signed range).

   Keep complete-operation controls: a flat call query does not establish flat
   folding, and a flat constant-range fold does not establish bounded symbolic
   or wide-range checking. Prefer indexed, selected-piece construction or an
   explicit proof repair; do not restore implicit candidate search in loan
   planning or move it into another non-expandable tactic.

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
