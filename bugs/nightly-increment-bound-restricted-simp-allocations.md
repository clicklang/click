# Restricted increment-bound simp exceeds its allocation bound

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491` in nightly 38149193625 and locally:

```sh
cargo nextest run --lib --profile nightly --run-ignored all -E 'test(increment_bound_family_retains_two_indexed_theorem_premises)'
```

At size 16 restricted incremented-order simp allocates 873 persistent nodes,
against the existing bound of 864. Preserve the selected two-premise theorem,
rejection when either premise is omitted, and the unchanged multi-size bound.
