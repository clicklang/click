# Chosen-body projection allocation test varies between repeated samples

The deterministic scaling regression
`surface::proof::proof_object::tests::choose_projection_walk_is_deterministic_across_selected_body_sizes`
intermittently fails its exact allocation-count comparison when run with
neighboring tests. Running it alone passed. This makes the library gate flaky;
no proof acceptance or incorrect projection was observed.

## Reproduction

With `RUST_MIN_STACK=8388608`, run:

```sh
cargo test --lib surface::proof::proof_object::tests
```

On the pointer-result branch this failed with 122 tests passing and one failure:

```text
walk allocation work must be deterministic at 32
left: 3049
right: 3047
```

A full `cargo test --lib` run also failed the same assertion at size 128
(15766 versus 15764); all other 5114 active tests passed. A previous full run
passed this test. The same failure reproduces before the pointer fix at commit `75565acbf`:
three runs of the 123-test suite passed, then the next failed at size 128
(15764 versus 15766). This establishes that the failure predates the fix.

The measurement uses the thread-local persistent-node allocation counter,
so interference through a shared counter is not established.

## Intended regression and acceptance

Reduce the variation in the existing test across selected body sizes
8, 32, 128, and 512. Determine whether unrelated interning/identity history
changes the measured data structure or whether the measurement includes
unrelated work. Make the projection measurement deterministic and retain its
near-linear scaling check, including runs alongside neighboring tests.
Do not fix this by removing the scaling coverage or increasing its tolerance
without accounting for the measured work.
