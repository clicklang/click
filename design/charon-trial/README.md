# End-to-end Charon adapter trial

This opt-in trial imports unchanged `trial.rs` through Charon and checks its
three contracts with Click's existing execution, memory, and certificate rules.
The scalar increment and the increment inside an owned guard both use ULLBC
control flow. The latter restores the caller's value on early return and after
a whole-value move followed by explicit drop. It has no whole-function HIR/MIR
coverage switch and no generated processed count.

The trial is narrower than the existing frontend. It accepts `i32`, `u8`, `u16`,
`u32`, bools, scalar/reference locals and fields, flat structs, direct local
calls, scalar casts, comparisons, checked addition/subtraction/multiplication,
acyclic branches, whole-value moves, and precise drops. Arrays, slices, loops,
general traits/generics, nested owned fields, and returned references are not
enabled by this adapter yet. Extraction coverage in the
[assessment](../rust-charon-assessment.md) is broader than checked coverage here.

## Build and reproduce

Click uses its normal stable compiler. The optional external Charon driver
needs `nightly-2026-09-17`, compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, with `rustc-dev` and `rust-src`.
The build script downloads the pinned, unmodified Charon revision
`5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` into `target/charon-source` and builds
the wrapper and driver in `target/charon`. It does not change Click's default
toolchain or the legacy exporter's pin.

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
export CLICK_RUST_EXPORTER="$(scripts/build-rust-exporter.sh)"
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_trial_live_refresh_and_compiler_rejections)'
```

Each external compiler invocation uses the existing owned process containment
boundary, with a 30-second deadline and bounded diagnostic output. These are
compiler crash-containment limits, not proof-search budgets.

## Profile, locks, and trust

Configuration schema 3 with `backend: "charon-trial"` selects this path. The
artifact is an envelope around Charon's typed `CrateData`, deserialized through
the pinned `charon_lib` without its rustc feature. The wrapper revision and
compiler commit are checked during refresh. The lock binds source, configuration,
artifact, wrapper and driver hashes, compiler/extractor revisions, and the
adapter/model profile. Ordinary verification reads locked inputs without running
either binary. Partial artifacts and incompatible options/profiles are rejected.
Only one source file with the locked contents is accepted.

The profile is Rust 2024 on `x86_64-unknown-linux-gnu`, panic abort, overflow checks
on, and MIR optimization level zero. It deliberately requests **optimized MIR**:
Charon's earlier-phase fallback cannot silently change the selected phase.
Constant/global initializer paths and dependencies with unmodeled bodies are
outside the accepted slice. Precise drops and ULLBC are required. No preset,
index-to-call, operation-to-call, or borrow-check bypass is enabled.

The one newly selected transform, `reconstruct_fallible_operations`, replaces
the overflow tuple/assert pattern with a panic-on-overflow operation. This loses
unwind detail, which the abort profile excludes. The adapter accepts only the
assessed operators and overflow modes; Click reintroduces their checked range
obligations. Neither wrapping nor unchecked arithmetic receives checked Rust
semantics accidentally. Charon clears consumed rustc arguments in its serialized
options, so the refresh-owned envelope separately records the exact compiler
flags and checked compiler identity.

The named interpretation `flat-record-drop-v1` covers compiler-generated
`Destruct` glue and compiler-resolved `mem::drop` for local flat records whose
fields are scalars/references. It invokes the imported, independently checked
`Drop::drop` method once and consumes the owned value. Resolution uses declaration
and trait IDs, lang/diagnostic items, and the glue receiver type; lookalike names
are insufficient. Generated glue is not separately verified as arbitrary raw
pointer code. Wider owned fields, cleanup effects, and library models need new
assessed interpretations or verified imported bodies.

The trusted compiler/extractor/adapter establishes correspondence with Rust;
the shared checker establishes the claims and rejects forged resource transfers.
rustc still establishes source borrow legality. Live loan graphs are not added
by this increment. The normalized CFG temporarily uses the existing internal
Rust vocabulary and local names. This trial does not complete the planned stable
proof-observation interface or compact array/kernel work.

## Migration decision

Successful checked arithmetic, owned cleanup, negative authority cases, and
proof-tool agreement justify proceeding toward Charon as the Rust extraction
boundary. Keep this explicit opt-in until existing supported fixtures have
equivalent coverage, named library models, stable source/proof observations, and
scaling evidence. Extend the single ULLBC adapter rather than adding a fallback
to the legacy exporter per function. The next composition target is a borrowed
loop with a live guard; then bring conversions and compact arrays through the
same boundary before switching the default and retiring legacy extraction.
