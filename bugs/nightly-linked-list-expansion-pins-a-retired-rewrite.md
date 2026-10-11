# Linked-list expansion test pins a retired rewrite spelling

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491` in nightly 38149193625 and locally:

```sh
cargo nextest run --lib --profile nightly --run-ignored all -E 'test(linked_list_pipeline_has_no_outcome_fallbacks)'
```

The original linked-list example verifies and expansion succeeds. The test
requires an exact statement-5 snapshot rewrite that is absent from the current
certificate, and fails before independently checking the expanded proof.
Inspect the retained certificate and replace the stale assertion with a check
of the intended checked transport, preserving independent reverification.
