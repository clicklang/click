# Frozen Rust gate inputs

These twelve unchanged inputs separate proof regressions from compiler work in
`tests/rust_import.rs`. Each directory contains the source, pinned native
Charon artifact, import configuration, and input lock. Normal proof tests copy
these files to an isolated directory, assert that the source exactly matches
the test input, and load the checked import. They never fall back to compiler
extraction when a fixture is missing or stale.

The normal gate retains positive proofs, false claims, missing-authority
checks, and deterministic array scaling checks. Complete example profiling,
expansion, certificate rechecks, and audits run in separate nightly tests.
Compiler rejection, crate-input identity, and extraction reproducibility tests
also run nightly; they still invoke the real pinned compiler.

`gate_fixtures::frozen_gate_fixtures_match_live_charon_extraction` re-extracts
all twelve inputs in temporary projects and requires identical native
artifacts after relocating the one absolute source-path metadata field. It runs in `scripts/check.sh --nightly`. To deliberately refresh a
fixture after a compiler/model update, build the pinned Charon exporter and
run `click import lock design/charon-trial/gate-fixtures/<name>/borrow.click`.
The configuration determines the compiler input; proof sidecars remain in the
original test/example locations.
