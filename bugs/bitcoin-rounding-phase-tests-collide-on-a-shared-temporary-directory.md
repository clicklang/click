# Bitcoin rounding-phase tests collide on a shared temporary directory

Soundness: none. A test-harness defect: two tests fail spuriously when run in
one process.

## Violated invariant

Each test owns its scratch directory, so tests pass in any runner and any
order. `check_upstream_cpp_rounding_phase` in
`tests/bitcoin_core_money_range.rs` names its directory
`click-bitcoin-fee-frac-{name}-{process id}` and creates it with
`fs::create_dir`. Two tests that use the same fixture `name` in one process
build the same path, and the second panics at `create_dir` (line ~133).

## Reproduction

Run the nightly bitcoin tests in one process, for example
`cargo test --test bitcoin_core_money_range -- --include-ignored`. Two tests
sharing a fixture name fail at `create_dir`. Each passes alone, and the
gate's per-process runner (nextest) is unaffected.

## Acceptance

- The scratch directory is unique per call (for example `tempfile::tempdir`),
  and the bitcoin tests pass together in one `cargo test` process.
