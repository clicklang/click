# Audit of the Adler public checksum writes `by arithmetic_certificate` without a call

`click audit` must rewrite a smart site into a simple certificate that
parses and verifies. On the public Adler checksum proofs, the audit's
rewrite of the `adler32_slice` contract prints a `by` followed by a bare
tactic name, which the parser refuses:

```text
CLAIM [1/1] borrow.click  __rust_q_I6_adler2_I13_adler32_slice.contract (1 sites) ... FAIL
    borrow.click:1675: expected a proof after `by`, got `arithmetic_certificate`: write one tactic call such as `arithmetic_certificate();`, or a block `{ ... }`
      error kind: syntax error
```

Reproduction: the nightly tests in `tests/rust_import/adler2_helpers.rs`
`adler2_helpers::charon_adler2_public_checksum_tools_recheck_original_contracts`,
`adler2_helpers::charon_adler2_public_boundaries_tools_check_all_original_bodies`
and `adler2_helpers::charon_adler2_public_serial_tails_tools_check_all_original_bodies`
(about 2 minutes each; need the pinned Charon:
`CLICK_CHARON=target/charon/debug/charon RUST_MIN_STACK=8388608 cargo nextest
run --profile nightly --test rust_import --run-ignored all -E 'test(=...)'`).
Each runs `verify` and `profile`, which pass, then
`click audit --start-at <the have of to_integer(__rust_mir_0)> --max-sites 1`,
which fails as above. The tests print only the audit's stderr ("1 expansion
audit check(s) failed"); the message above is from its stdout. Reproduced on
2026-10-11 at master `9d5f338e`.

The printer emits an `arithmetic_certificate` step in the `by TACTIC;` short
form without its call parentheses, or emits a tactic name where only a call is
accepted. Start by running `click expand` on the same site and reading the
printed line.

Acceptance:

- whatever `click expand` and the audit rewrite print for an
  `arithmetic_certificate` step, the parser reads back;
- a small regression (an mdtest or unit test) that prints and parses back the
  short `by` form of that step;
- the three nightly tests above pass, and they report the audit's stdout on
  failure.
