# Expanded memcpy proof work grows with unrelated allocations

Checking a fixed additional memcpy must follow its selected state delta,
not repeatedly scan unrelated live allocations or proof history.

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491`:

```sh
cargo nextest run --lib --profile nightly --run-ignored all \
  -E 'test(expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations) or test(expanded_roundtrip_work_per_source_byte_is_logarithmic)'
```

At 1, 2, 4, and 7 unrelated allocations, the extra memcpy's deterministic
work is 2,872, 2,895, 2,941, and 3,018 units, exceeding the existing bound
of four additional units per doubling. Whole-proof work per source byte
also grows from 19.25 to 24.22 instead of following its logarithmic bound.
Attribution points to simple `step`, proof completion, and heap-free
checking. Both regressions failed in nightly run 38059800813.

Acceptance: both unchanged deterministic multi-size regressions pass;
authority, memory-state equality, path coverage, and return certification
remain checked; no increased budgets, relaxed scaling thresholds, or
source-program changes hide the problem.
