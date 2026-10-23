# The listed-order-chain scaling test depends on thread timing

Soundness: none. A test-harness defect: a deterministic scaling regression is
not deterministic under `cargo test`.

## Violated invariant

Scaling regressions are deterministic across runners
(`docs/internals/verification-efficiency.md`).
`listed_order_chain_arithmetic_is_near_linear_in_the_chain`
(`src/scaling_tests/surface/tests/scaling_tests.rs`) fails under plain
`cargo test --lib`: which size sample pays a one-time setup cost depends on
which thread first reaches shared lazily initialized state. The measured
numbers are identical on master, and the test passes under the gate's
per-process runner.

## Reproduction

`cargo test --lib listed_order_chain_arithmetic_is_near_linear_in_the_chain`
alongside the rest of the lib tests (default test threads); it fails
intermittently. Run alone or under nextest, it passes.

## Acceptance

- The test warms the one-time state before measuring, or measures work
  units that exclude it, and passes under `cargo test --lib` in a full run.
