# Arena pipeline expansion exhausts a quantified `have` control budget

Soundness: not soundness. The unchanged arena proof verifies, but expansion
cannot construct and check its explicit certificate within an existing control
work bound. No false acceptance is known.

Reproduced on `163709ed8` after the scalar-frame refusal repair (#1273), using
the current debug CLI:

```sh
click audit --claim arena_pipeline.contract examples/arena
```

The audit inventories 334 selected smart sites in `arena_pipeline.contract`.
Its original-sidecar session succeeds (16,290,482 deterministic units locally).
The whole-claim audit then fails while cold targeted verification of the
original claim is running (the expanded proof is checked concurrently):

```text
`arena_pipeline.contract` tactic 48: `have` failed for
`forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 }`:
verification budget exhausted inside tactic `have` ...
after 2500001 units (2500000 limit; statement 17, source tactic 58)
location: tactic 58 > have body tactic 7 > have body tactic 9
```

The failure is the zero-initialization claim after `arena_free(first)` in
the second-allocation failure branch of `examples/arena/arena_cells.click`,
around line 2865. Its nested proof combines the cleared region with the
unchanged cells outside that region. The failing atomic goal is a zero-valued
memory read; the diagnostic reports unsuccessful separation checks across
call/read memory snapshots. Do not infer a missing premise from those
observations alone.

A direct cold reproduction, without the audit's discovery and retained-session
setup, is:

```sh
click expand --claim arena_pipeline.contract --output /tmp/arena-pipeline-expanded.click \
  examples/arena/arena_cells.click
```

It fails while checking the original proof, before producing an expansion.
Thus the original session's success does not establish that cold targeted
verification fits the same tactic budget.
`CLICK_TIMINGS=1` reproduces the same work-budget failure. Its diagnostic's
completed-operation attribution identifies 1,317,704 units in
`simp selected premise reduction`, 517,450 in
`simp closure: indexed goal equality rewrite`, 191,153 in atomic-load
canonicalization misses, 190,349 in cell-epoch walks, and 135,269 in premise
spelling. These nested counters overlap; do not sum them. The original
successful quantified `have` costs 1,983,537 units in each original pass.
Raw logs interleave other proof paths, so use the diagnostic's scoped
attribution rather than aggregating everything between two tactic log lines.

The largest attributed operation is
`reduce_simp_atomic_premises` in
`src/surface/planning/proposition_search.rs`: legacy atomic evidence retains a
connected component, and smart planning repeatedly tries restricted contexts
to remove premises before source spelling. Investigate how the selected
memory-read derivation can retain its actual dependencies and how indexed
equality rewriting contributes the additional work. These are investigation
leads, not an established root cause or a justification to remove required
premises. Diagnose the checking/certificate path before changing search or
expansion.
The retained load-address-congruence producer now accepts an exact same-base
pointer premise through its offset view, with a regression covering connected
aliases, field displacements, and withdrawal. That fixes a separate evidence
selection gap found during investigation, but does **not** fix this arena
reproduction: direct cold expansion on the repaired branch still reaches
2,500,001 units at the same obligation. Its completed-operation report is
unchanged from the immediately preceding baseline on `e0a7f03ba` (1,482,735
units in premise reduction and 534,387 in indexed equality rewriting). The
actual selected read pairs therefore still miss that same-snapshot evidence
route. Inspect their registered origins and canonical projection provenance
before assuming that differing epochs are interchangeable; no such extension
has been implemented or validated here.

Preserve the existing C, proof claims, all 334 selected sites, and work bounds;
`--max-sites 1` does not exercise the whole-claim path.

Acceptance: the named whole-claim audit passes at unchanged limits, including
retained and cold rechecking and deterministic performance comparison. Add a
small deterministic multi-size regression preserving the identified repeated
work, and run the normal scaling controls for any representation change.
