# Execution theorem application exceeds its allocation bound

Soundness: not soundness. An existing checked theorem-application allocation
regression fails its deterministic local-update ceiling; no false acceptance is
shown.

Priority: P2.

On unchanged master `2cee79c02`, run:

```sh
cargo nextest run --lib --profile nightly --run-ignored only \
  -E 'test(=surface::proof::proof_object::tests::execution_apply_uses_only_named_evidence_and_forks_persistently)'
```

The original first sample fails:

```text
size 16 theorem application allocated 307 persistent nodes (bound 288)
```

The test supplies named theorem evidence on an execution frontier, checks that
unrelated facts stay shared, and measures only the checked application. Preserve
its original theorem, selected premises, transactional rejection cases, and all
sample sizes while investigating the extra allocations. A first-size failure
alone does not establish its scaling cause.

Acceptance: the original test passes at every size with the existing allocation
ceiling and proof assertions. Do not increase the bound to mask the failure.
