# Early-return checking loses its whole-proof scaling bound

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491` in nightly 38149193625 and locally:

```sh
cargo nextest run --lib --profile nightly --run-ignored all -E 'test(completed_early_return_contexts_are_reused_for_certification) or test(indexed_simp_premises_reduce_whole_early_return_work)'
```

Both multi-size regressions fail their whole-verification bounds for the original
fan-out program. Shared execution-fact storage passes; attribution includes
completion and finishing work. Both unchanged regressions must pass, including
explicit proofs and rejection of a false final path. Do not relax bounds.
