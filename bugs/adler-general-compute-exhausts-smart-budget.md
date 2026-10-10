# The Adler whole-computation nightly proof exhausts its smart work budget

## Violated invariant

The checked-in positive nightly regression for the original Rust Adler
computation should verify with its ordinary deterministic work limits. It
currently refuses an execution prefix before the tail loop.

## Reproduction

With the repository's Rust import toolchain configured:

```sh
CLICK_CHARON="$(scripts/build-charon.sh)" cargo nextest run \
  --profile nightly --test rust_import --run-ignored only --no-capture \
  -E 'test(charon_adler2_general_compute_proves_original_body)'
```

The test returns a proof error from `execute_until`: 2,000,001 smart work
units against the 2,000,000 limit, at statement 1126/source tactic 912 in
the imported `Adler32::compute` contract. The original prefix is
`execute_until(loop(5))` in
`design/charon-trial/adler2/general-compute.click`.

This reproduces on pre-#598 commit `993a2d7a7` and on the range-audit
commit `bcf1e53a8`; it is independent of those bug fixes. Whole-test runs
took approximately 225–234 seconds. Operation attribution identifies
execution assignments, call assignments and call requirement checking.

Stopping at `assignment(__rust_mir_138_remaining, 0)` is still too late:
the first prefix exhausts the same limit. Inheriting only proof marks,
or restricting automatic snapshot spelling candidates, does not fix it.

## Acceptance criteria

- The existing positive nightly regression passes with its ordinary budgets.
- Keep the original Rust implementation and the contract's claims unchanged.
- Repair the proof with earlier relevant execution boundaries, or reduce
  unnecessary execution work; do not raise or disable verification budgets.
- If kernel work changes, cover its work bound with a focused regression.
