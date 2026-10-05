# A deferred Charon expansion selects cases using a dead compiler local

## Violated invariant

A verified smart tactic must expand into a certificate that re-verifies at
that same source occurrence. Native Charon execution verifies `choose` in
`examples/basic-rust/borrow.click`, but expanding its final `simp()` emits
`if __rust_checked_2 < 7` after `execute()`. That compiler temporary is no
longer available at the return frontier. Auditing this occurrence fails,
although expanding the whole claim succeeds and re-verifies.

Reproduced on `fe80441b60672facef9d2754f96a351adef4906d` during the attempt
to retire the legacy extractor. No Rust source or contract changes are needed.

## Reproduction

Build Click and use the checked-in, locked native inputs:

```sh
cargo build --bin click
target/debug/click verify examples/basic-rust/borrow.click
target/debug/click audit --claim choose.contract \
  --start-at examples/basic-rust/borrow.click:8:5 --max-sites 1 \
  examples/basic-rust/borrow.click
```

Verification passes. The audit reports that tactic 1, a proof-level `if`,
cannot be certified in this execution context. The API
`expand_program_prepared_tactic_source_at(sidecar, prepared, 8, 5)` exposes
the unverified rewrite: it preserves `execute()` and replaces `simp()` with
an `if __rust_checked_2 < 7` whose arms normalize the result using
`at(function.entry, x) < at(function.entry, 7)` and its negation.

The suspected boundary is the deferred expansion's `branch_skeleton`,
created from the execution certificate in
`src/surface/proof/proof_object/execution_entry.rs` and grafted around
path-dependent closers in `src/surface/proof/claim_proofs.rs`. The skeleton's
condition can be valid at its original execution frontier without being
valid after execution. A trial that tried re-synthesizing the guard from the
return state's lowering did not repair this case; it is not a checked fix.

## Intended regression

Capture the final `simp()` in this unchanged native fixture and re-verify its
returned source through both the prepared API and the retained audit session.
Also exercise a mutated parameter and nested conditions so a repair cannot
substitute entry values for unrelated later values.

## Acceptance criteria

- The isolated occurrence audits successfully and its expansion re-verifies.
- Whole-claim expansion and ordinary verification continue to agree.
- Case selectors have checked meaning at their new frontier; no compiler-local
  aliases, weakened claims, fixture exceptions, or additional search budgets
  hide the lost scope.
- The regression runs in the normal gate before legacy extraction is retired.
