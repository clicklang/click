# Nightly uint64 truncation certificate work is not perfectly flat

Soundness: not soundness. The existing regression proves its positive
truncation claims, then fails a deterministic-work assertion before reaching
its final full-width negative controls. This does not demonstrate acceptance
of a false claim.

Reproduced on upstream `e29e1958e` with:

```sh
cargo test --lib \
  kernel::proof::fact_reasoning::uint64_loop_tests::scaling_tests::uint64_truncation_certificates_require_full_width_bounds \
  -- --exact --ignored --nocapture
```

The test in `src/scaling_tests/kernel/proof/fact_reasoning/uint64_loop_tests.rs`
normalizes a signed comparison of truncated uint64 values using two named
premises: a strict full-width order and an `INT32_MAX` upper bound. It adds
8, 32, 128, and 512 unrelated bounds, measures each successful normalization,
and requires exactly the same charged work at every size.

The assertion at line 108 fails with `[49, 50, 49, 50]` (exit 101).
An earlier survey on `211094055` produced `[49, 49, 49, 50]`, also failing.
After rebasing onto upstream `4d4407570`, a fresh process still fails at
the same assertion with `[50, 49, 49, 50]` (exit 101).
All four positive normalizations and the per-size missing-premise checks
finish before this assertion. The subsequent `2^32` bound rejection and
signed/low-bit equality controls are not reached.

Acceptance criteria:

- Attribute the one-unit variation to the operation charging it. Determine
  whether it is expected indexed bookkeeping or unwanted ambient work.
- Make the regression enforce the intended complexity without requiring
  accidental identical counts. A revised bound must still reject an ambient
  scan; shrinking the fixture until the assertion passes is insufficient.
- Preserve and execute the missing-bound, too-wide-bound, and signed/low-bit
  semantic controls, across multiple fresh test processes.
