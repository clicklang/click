# Nightly vector expansion still reads a deleted mdtest

The nightly `vector_field_input_pointer_certificates_round_trip` regression
must have a committed fixture. Master `486e8097` deleted its mdtest input
while replacing redundant gate fixtures, but left this independent nightly
expansion/recheck test reading the old path.

Reproduced with:

```sh
cargo nextest run --lib --profile nightly --run-ignored all \
  -E 'test(=surface::tests::expansion_tests::vector_field_input_pointer_certificates_round_trip)'
```

It panics at `read_to_string(...).unwrap()` with `No such file or directory`
for `mdtests/composite_resource_vector_fill_loop_snapshot.md`.

Acceptance: preserve the original vector-field/entry-pointer expansion and
complete-claim recheck coverage with a committed nightly-only fixture;
the regression passes without reinstating redundant gate verification.
