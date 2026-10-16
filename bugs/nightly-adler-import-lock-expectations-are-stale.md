# Adler import-lock mutation tests expect obsolete error wording

Soundness: not soundness. The importer correctly refuses modified Rust
modules. The nightly tests fail because their expected text describes an
older lock diagnostic; no false acceptance is known.

The October 16 nightly fails these existing tests in
`tests/rust_import/adler2_helpers.rs`:

- `charon_adler2_helpers_prove_all_lanes_and_lock_original_modules`
- `charon_adler2_incremental_client_live_refresh_checks_the_input_closure`
- `charon_adler2_resumed_client_live_refresh_checks_the_input_closure`

The first expects `lock differs`; the other two expect
`lock differs from its inputs`. The importer instead reports
`Rust source <path> differs from its import lock; run click import lock`.
Reproduced the first test's assertion failure locally. Also copied the locked
`design/charon-trial/adler2` fixture and independently replaced each of
`src/lib.rs`, `incremental.rs`, and `resumed.rs`: verifying a sidecar naming
that source reports this module-specific rejection in all three cases.

Reproduce the first test with:

```sh
cargo nextest run --profile nightly --test rust_import --run-ignored only \
  -E 'test(=adler2_helpers::charon_adler2_helpers_prove_all_lanes_and_lock_original_modules)'
```

Keep the source mutations and the positive import/proof/refresh checks.
Match the specific modified module and current imported-source rejection;
an arbitrary preparation failure is insufficient. The three named tests
should pass without changing importer behavior or weakening lock checking.
