# Early-return paths are finished and certified from their whole prefix

Soundness: not soundness. This is a scaling defect in simple checking and
certification of a proof that verifies; no claim is accepted or refused
differently because of it.

The violated invariant is the [complexity
contract](../docs/internals/verification-efficiency.md#complexity-contract)
and its [output-sensitive
exception](../docs/internals/verification-efficiency.md#output-sensitive-exceptions)
for branching: repeated branching "should share common prefixes and cost no
more than the explicit path structure it checks". A loop-free function with
`N` sequential early returns has a fully expanded proof linear in `N`, but
path `k` carries `k` path facts (`x != 0` ... `x != k - 1`) and `k` stores, and
the operations below rebuild or re-check that whole prefix once per path. The
total is quadratic in `N`, and expansion cannot help: none of it is smart
search.

## Reproduction

```c filename=mark.c
int32 mark(int32 *a, int32 x) {
    a[0] = 0;
    if (x == 0) { return 1; }
    a[1] = 1;
    if (x == 1) { return 1; }
    /* ... the same two lines for each k up to N - 1 ... */
    return 0;
}
```

```click
verifying "mark.c";
int32 mark(int32 *a, int32 x) {
    owns a[0..N];
    ensures result >= 0;
}
```

`early_return_project` in
`src/scaling_tests/surface/tests/scaling_tests.rs` generates both. Measure
simple checking alone on the expansion:

```console
click expand --output out.click mark.click:5:1
click profile --top 60 out.click
```

Release build, 2026-10-20, after the trace borrowing, terminal-join and
storage-check fixes landed. Named deterministic work of the expanded proof at
8, 16, 32, 64 and 128 returns:

| operation | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| `proof context finishing` (all of `finish_ordered_proof`) | 7,393 | 15,097 | 33,577 | 82,825 | 230,473 |
| `proof completion` | 663 | 2,139 | 7,587 | 28,467 | 110,163 |
| `contract path preparation` | 1,843 | 4,127 | 10,423 | 29,927 | 96,583 |
| `contract claim: proposition` (contains the preparation) | 1,924 | 4,280 | 10,720 | 30,512 | 97,744 |

Every other named operation is linear (for example `execution path
finishing`: 6,588 / 12,492 / 24,300 / 47,916 / 95,148). Wall time of the
expanded proof is 0.30 s at 32, 0.64 s at 64 and 2.6 s at 128 returns.

## Causes found

Each is a per-path rebuild or re-check of facts the same session produced
along the shared prefix, so the fixes are construction, not re-validation
([guide](../docs/internals/verification-efficiency.md#construction-not-re-validation)).

1. `proof completion`, `ExecutionProofCore::checked_execution_paths` in
   `src/kernel/proof/execution.rs`:
   - `trace_completion_from_entry` checks every fact of a return proof's
     base introduced since the checked entry against the path
     (`delta.iter().chain(extra.iter())`, one work unit and a
     `proves_exact` each). The base is the proof object's own facts on this
     path, so this is all `k` path facts, re-validated.
   - `retain_return_context` imports the return context's whole fact stream
     with `facts_not_assumed_by`, which walks all of it.
   - `boundary_assumptions` and `post_assumptions` are rebuilt per path from
     the candidate's whole fact and effect streams.
   - A trace ending in return propositions is completed twice
     (`publication_completed` re-runs `trace_completion` on the prefix).
2. `contract path preparation`, `prepare_function_claim_path` in
   `src/kernel/api/contract_certification/contract_claims.rs`: when the entry
   resources have observable facts (they do for `owns a[0..N]`), the path's
   assumptions are rebuilt from `path.execution_facts()`, which also merges
   the fact and effect streams into a fresh index per path.
3. `Proof::split_function_outcomes`
   (`src/surface/proof/proof_object/outcomes_and_focus.rs`): each outcome
   goal imports the path's whole effect stream into its retained leaf
   `ProofFacts` with `with_kernel_checked_fact` (2,144 indexed insertions at
   64 returns) and materializes `path.execution_facts()` again for
   `OutcomeProofCore::effect_facts`. This cost is mostly uncharged.
4. Terminal joins republish every path of both arms. Since the fix they no
   longer copy a path's facts, but each enclosing join still visits each
   deeper path once (provenance, route decision, dedup key), so a chain of
   `N` returns makes `O(N^2)` constant-cost visits.

A shared fix is a context built along the path tree rather than per path:
each prefix's facts are admitted once into a persistent context, and a path
extends its parent's context by its own suffix (the facts and stores after
its last branch). The traces already share their prefixes as
`PersistentSequence` nodes.

## Intended regression

Add to `src/scaling_tests/surface/tests/scaling_tests.rs`: expand
`early_return_project` at 8, 16, 32 and 64 returns outside the measurement,
verify each expansion with `scaling_sample`, and require each of
`proof completion`, `contract path preparation`, `contract claim:
proposition` and `proof context finishing` to grow at most 2.25x per
doubling. At the sizes above it fails at 3.2x to 3.9x. If it exceeds about
2 s in a debug build, mark it `#[ignore = "nightly: ..."]` and keep a
smaller gate variant.

## Acceptance criteria

- The regression above passes; on the representation this file describes it
  fails.
- The four operations are linear in the expansion, or a per-path cost that is
  genuine output (a path theorem that must state its own facts) is
  documented in the verification efficiency guide with its measured curve.
- `completed_early_return_contexts_are_reused_for_certification`, the
  `early_return_execution_expansion_reverifies_*` tests and
  `one_hundred_twenty_eight_early_returns_expand_and_reverify` still pass,
  and a false final path (`return -1;`) is still refused.
