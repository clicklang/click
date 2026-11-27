# Native Charon Rust adapter

The native adapter imports unchanged `trial.rs` through Charon and checks its
three contracts with Click's existing execution, memory, and certificate rules.
The scalar increment and the increment inside an owned guard both use ULLBC
control flow. The latter restores the caller's value on early return and after
a whole-value move followed by explicit drop. It has no whole-function HIR/MIR
coverage switch and no generated processed count.

The [Rust reference](../../docs/reference/rust.md) and
[coverage matrix](../../docs/reference/coverage.md) define current support.
This directory holds locked source/contract regressions and historical frozen
proofs; extraction coverage alone is not checked language support.

## Migration completion

Charon is the default and sole Rust extraction backend. Schema-3 configs may
omit `backend`; `charon` and the historical `charon-trial` alias select the same
path. Schema 2 is rejected before extraction or output mutation. The old
repository-owned exporter, compiler pin, build script, and CI runtime have been
removed. No function or artifact can fall back to legacy extraction.

All 16 canonical examples use the implicit native backend with their original
Rust bodies and contracts. The 72 original regression responsibilities are
retained: compiler-backed checks run against actual native artifacts, and serialized move/drop
corruption coverage now calls the lowering/kernel directly instead of forging
legacy JSON into a ULLBC file. Newly supported source patterns have positive
proofs and false-claim or authority negatives. Native iterator-state assertions
replace old JSON shapes and generated processed counts; loop proofs use semantic
frontiers. Standard unsigned identity `From<T>` calls are checked against their
resolved generic signature (`unsigned-from-v2`), with forged-signature negatives.
Borrowed iterator forwarding validates the resolved standard trait, implementation,
and associated-item signature, then keeps the concrete iterator's single state.
This preserves `for chunk in &mut chunks` and subsequent remainder access.
Extraction normalizes temporary output metadata so repeated refreshes, including
configs sharing an artifact, produce stable bytes and valid locks.
All 52 native configurations were refreshed through the pinned extractor.
Validation includes the original compiler-backed regression responsibilities,
native adapter/lowering and proof-tool checks, 20 live extraction tests, the
quality/setup gate, and 31 documentation checks.

CI builds and archives Charon and its driver once, restores the profile-derived
compiler runtime for archive consumers, and runs the live extraction gate. The
[original checkpoint record](https://github.com/clicklang/click/blob/2175760b9/design/charon-trial/README.md)
preserves the intermediate percentages and migration gates. Completion
of the backend migration does not imply support for all Rust or whole crates.

## Build and reproduce

Click uses its normal stable compiler. The external Charon driver
needs `nightly-2026-09-17`, compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, with `rustc-dev` and `rust-src`.
The build script downloads the pinned, unmodified Charon revision
`5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` into `target/charon-source` and builds
the wrapper and driver in `target/charon`. It does not change Click's default
toolchain.

```sh
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component rust-src
scripts/build-charon.sh
cargo run --bin click -- import lock design/charon-trial/trial.click
cargo run --bin click -- verify design/charon-trial/trial.click
cargo run --bin click -- profile design/charon-trial/trial.click
cargo run --bin click -- audit design/charon-trial/trial.click
```

To inspect a generated certificate, expand `guarded_increment.contract` with
`--in-place` and verify the resulting sidecar through the ordinary entry point.
Keep experiments in a task worktree and restore the checked fixture afterwards.
The ordinary `rust_import` regressions perform this operation in a temporary
project and check false results, possible overflow, missing memory authority,
and incorrect restoration. Unit regressions deliberately corrupt the normalized
ownership events and check that the shared engine rejects duplicate moves,
duplicate drops, missing cleanup, and reads after move.

The normal repository gate uses the checked-in artifact and lock; it requires
neither Charon nor this extra nightly to load and verify them. The separately
invoked live compiler regression refreshes through the real extractor and checks
E0506/E0382 rejection without publishing an artifact:

```sh
export CLICK_CHARON="$(scripts/build-charon.sh)"
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_trial_live_refresh_and_compiler_rejections)'
```

Each external compiler invocation uses the existing owned process containment
boundary, with a 30-second deadline and bounded diagnostic output. These are
compiler crash-containment limits, not proof-search budgets.

## Profile, locks, and trust

[charon-profile.json](../../src/languages/rust/charon-profile.json) is the
machine-readable authority for compiler/extractor pins, flags and semantic
versions. The default profile uses optimized MIR, ULLBC, precise drops,
overflow checks and panic abort. `reconstruct_fallible_operations` replaces
compiler overflow/assert and indexing patterns; the adapter restores the
corresponding arithmetic and bounds obligations in the shared engine.
No preset or borrow-check bypass grants additional semantics.

The compiler/extractor/adapter establishes Rust-to-model correspondence;
rustc establishes source borrow legality. Click checks the submitted functional
claims, memory authority, initialization and cleanup through the shared engine.
Resolved external library models are named assumptions, not verification of
their Rust implementations. Lookalike names must not acquire those models.
Production local-reference coverage is recorded in the
[borrow-authority assessment](../rust-borrow-authority-assessment.md).

Locks bind source/configuration, selected artifacts, compiler/extractor and
adapter/model identity. Verification loads locked artifacts offline; refresh
runs the compiler. Partial artifacts and incompatible identities are refused.
Crate closure and dependency admission follow the current reference and
[Rust delivery item](../../roadmap/rust-support.md), not the old single-file
trial restrictions. Interpretation changes version their named profile entry
and deliberately refresh affected locks.

## Complete canonical proof-port adoption

The [parity inventory](parity.json) distinguishes current canonical examples,
verified proof ports, and archived original sidecars. All 16 original source
and contract pairs were adopted with native imports. Five proofs needed ports
away from legacy temporary names or numeric frontiers; their original Rust,
signatures, specification functions and contracts were preserved.

The archived proofs received their initial syntax respelling on 2026-10-26.
The 2026-11-15 `rewrite` migration changed equality arguments to two expression
arguments and refreshed affected `frozen_sha256` digests. `original_sha256`
continues to identify the originals in history. The `normalize()` retirement
respells the two remaining archived proofs and refreshes their frozen digests.
The chunk archive now reaches a later cast bound before its proof gap. Literal
archived-sidecar compatibility was 11/16. That is a
historical compatibility measure, not current Rust coverage or an unfinished
backend switch. The live tests check frozen outcomes separately from current
canonical proofs; an old failure is not counted as a current passing proof.

## Fixture guide

| Responsibility | Fixtures |
| --- | --- |
| Calls and callable contracts | `function-pointers`, `extern-functions`, `closures`, `capturing-closures`, `impl-fn`, `parameterized-contracts` |
| Construction, storage, copies | `constructors`, `plain-record-loop`, `copy-after-call`, `loop-array-copy`, `array-values` |
| Bounds and compact arrays | `array-lengths`, `scalar-constants`, `gate-fixtures` |
| Slice/chunk values and loops | `split-slices`, `slice-iter`, `chunk-proof`, `chunk-view-loop`, `chunk-lane-results`, `iterator-proof`, `into-slices`, `loop-headers` |
| Whole-program checksum composition | [adler2](../adler32/project/adler2/README.md) and the [C/Rust demonstration](../adler32/project/checksum-correspondence.md) |

The per-fixture READMEs identify distinct source patterns, trust restrictions
and rejection controls. Their old parity totals describe intermediate
checkpoints. The [historical ledger](https://github.com/clicklang/click/blob/2175760b9/design/charon-trial/README.md)
contains the removed rollout narrative; tests, locks and frozen source inputs
remain the executable record.
