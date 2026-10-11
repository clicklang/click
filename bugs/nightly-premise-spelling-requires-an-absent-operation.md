# Premise-spelling regression fails when no premise needs spelling

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491` in nightly 38149193625 and locally:

```sh
cargo nextest run --lib --profile nightly --run-ignored all -E 'test(simp_premise_spelling_is_linear_in_early_returns)'
```

The proof verifies but the test panics at four returns because its named-work
map has no `simp closure: premise spelling` entry. Zero executions are a valid
outcome of a faster proof path. Cover that case while retaining a multi-size
regression that actually exercises premise spelling and its linear bound.
