# Charon extraction assessment for Click

Assessed on 2026-10-02. This is extraction evidence and an adoption proposal,
not a new supported frontend or a checksum verification result.

Follow-up: the [end-to-end adapter trial](charon-trial/README.md) connects the
candidate to Click's existing checker for arithmetic and owned guard cleanup.
It records a deliberately different MIR/transform selection and its trust
boundary; the extraction measurements below retain their original configuration.

## Recommendation

Charon is a credible foundation for Click's Rust extractor. A bounded live
probe extracted both the composition case that motivates consolidation and
the unchanged, pinned adler2 checksum path. Prefer a small end-to-end adapter
experiment over adding more independent HIR and MIR feature paths. Use
Charon's **ULLBC** (unstructured basic-block representation) as the candidate
semantic input, with a Click-owned representation and the existing checked
engine downstream. Preserve source metadata for sidecars and diagnostics.

This reuses compiler integration, resolved types/calls, places, checks, and
drop extraction. It does not supply Click contracts, library interpretations,
memory authority, loop invariants, or proof certificates. Aeneas's functional
interpretation of LLBC is a separate backend design; adopting Charon does not
require adopting that interpretation or replacing Click's memory model.

## HIR, THIR, MIR, and Verus

The useful simplified pipeline is HIR -> THIR -> MIR. HIR retains more source
structure; THIR follows type checking and makes adjustments such as
autoref/autoderef and resolved overloaded calls explicit. MIR makes evaluation,
moves, control flow, and cleanup explicit, with additional transformations at
successive MIR phases. Source structure is lost while useful semantic facts
are made explicit. HIR alone is not a complete substitute for type-checking
results, ownership analysis, or drop elaboration.

Click could implement some lowering itself. Every such operation then needs
faithful evaluation order, adjustments, moves, temporary lifetimes, and cleanup
semantics. Reimplementing the difficult part of rustc's lowering increases the
translator trust and maintenance burden. A source-facing HIR/THIR layer remains
useful, but it should annotate a single semantic body rather than introduce a
second meaning for Rust operations depending on whether a guard is present.

Verus has access to these compiler stages. Its architecture is commonly
summarized as HIR -> VIR -> SST -> AIR, but its driver explicitly describes
**HIR/THIR -> VIR** for verification and **HIR/THIR -> MIR** for executable
Rust, plus compiler lifetime checking and synthetic checks for ghost code.
There is no fundamental MIR-access limitation motivating its choice of VIR.
The choice reflects its proof language and interpretation. Borrow the separation
between compiler integration, semantic representation, and proof backend;
which execution/resource semantics Click supports still needs its own decision.

Sources: [rustc THIR guide](https://github.com/rust-lang/rustc-dev-guide/blob/master/src/thir.md),
[MIR guide](https://github.com/rust-lang/rustc-dev-guide/blob/master/src/mir/index.md),
[Verus architecture](https://github.com/verus-lang/verus/blob/main/source/CODE.md),
and [Verus driver](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/driver.rs).
The Verus links describe the inspected upstream architecture and are not an
input dependency of Click.

## Pinned extraction experiment

| Input | Selection |
| --- | --- |
| Charon | `0.1.279`, revision `5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` |
| rustc | `nightly-2026-09-17`, commit `923c95cdf5ba65cea505aa2ea829f578e1506ed8` |
| Target | `x86_64-unknown-linux-gnu` |
| Semantics | overflow checks on, panic abort, MIR opt level 0 |
| Extraction | ULLBC, elaborated MIR, precise drops, default installed sysroot |
| External library bodies | `core`, `alloc`, and `std` opaque |

No Charon preset was used. Borrow checking and type checking remained enabled.
Fallible-operation reconstruction, indexing-to-calls, and operations-to-calls
remained disabled, keeping explicit assertions and compact array operations.
The reproducer rejects failed or partial artifacts (`has_errors`). A separate
LLBC extraction of the composition source also succeeded; its reconstruction
scaling was not measured.

The composition source combines a restoring `Drop` guard, a mutable borrow,
`u16` arithmetic and `u32::from`, arrays, stored `chunks_exact` and its remainder,
shared byte iteration, indexed updates, an early return, a move, and explicit
drop. Companion functions expose overflow, bounds, division-by-zero, and shift
checks. A tuple-struct array with custom `AddAssign` tests resolved operators.

| Probe | Observed result |
| --- | --- |
| Composition `combined` | 60 blocks, 190 statements, 12 explicit assertions, one precise implicit drop, and the explicit `mem::drop` call |
| Arithmetic companions | One explicit assertion each for increment, indexing, division, and shift |
| Conflicting borrow | rustc E0506; nonzero exit and no extraction artifact |
| Use after move | rustc E0382; nonzero exit and no extraction artifact |
| Unchanged adler2 `adler32_slice` root | 15 translated bodies including generated glue; `compute` has 150 blocks |

The adler2 `lib.rs` and `algo.rs` bytes match
[the existing source manifest](rust-checksum-sources.json), revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`. Extraction used edition 2021 and the
`std` feature, preserving its tuple structs, custom operators, indexed updates,
and optimized loops. **The compiler differs from the manifest's June pin.**
This establishes compatibility with the inspected Charon/compiler pair, not
compatibility with the current production profile or verification of Adler-32.
Opaque library bodies require named interpretations or separately verified code.

Compactness and control-flow probes measured representation growth:

| Repeat length | Artifact bytes | Blocks | Statements |
| --- | ---: | ---: | ---: |
| 16 | 47,505 | 3 | 10 |
| 4,096 | 47,515 | 3 | 10 |
| 1,000,000 | 47,530 | 3 | 10 |

| Sequential branch diamonds | Blocks | Statements |
| --- | ---: | ---: |
| 8 | 57 | 74 |
| 32 | 225 | 290 |
| 128 | 897 | 1,154 |

The repeat retains one compact operation, and branch joins remain shared
(`7N + 1` blocks, `9N + 2` statements). These are extraction measurements,
not claims about Click checking time. Whole-array copy growth and unrelated
proof-context growth still need adapter/kernel regressions.

## Conditions for adoption

1. **Compiler and extraction identity.** This Charon pin needs a newer compiler
   than Click's exporter. Evaluate a coordinated profile update or an older
   compatible Charon revision; do not silently change the existing source lock.
   Bind the full extractor revision/binary, compiler, options, target/layout,
   modules, dependencies, and library models in prepared inputs. Charon's
   artifact version alone is insufficient. Use its typed library/schema for a
   production adapter rather than the probe's minimal JSON field inspection.
2. **Actual MIR phase provenance.** Charon's selected MIR phase can fall back
   to optimized MIR if an earlier body is unavailable; dependencies can only
   expose optimized MIR. The global option is not per-body provenance. Require
   explicit phase evidence or a justified policy for every accepted fallback.
   Reject partial artifacts and missing required bodies.
3. **Checked semantic mapping.** Preserve checks, typed places/projections,
   overflow modes, storage lifetime, move events, and resolved drop glue in one
   adapter. Maintain explicit panic obligations and Click's authority rules.
   Compiler-generated glue may use unsafe/raw operations even for safe source;
   distinguish that origin from admitting arbitrary unsafe Rust. An abort
   profile also needs a precise interpretation of unreachable unwind edges.
4. **Proof/source correspondence.** Item IDs, files, and spans are useful
   foundations, but MIR has lost source loop forms and some scopes. Define
   stable sidecar observations and loop/operation identities. Retain source
   metadata as needed without heuristic HIR/MIR matching or depending on
   temporary spelling. ULLBC keeps joins shared; avoid expanding paths while
   making control flow available to the existing engine.
5. **Library registry and resources.** Resolve supported instances by item and
   type arguments, with named contracts, effects, and panic behavior. Declared
   regions and reference types do not provide a body-level live-loan graph;
   Charon does not promise that information. Continue rustc borrow legality and
   checked Click permissions, and add compiler metadata if explicit loan
   recovery requires it. Compact extracted arrays still need compact shared
   kernel value/authority operations.

These conditions should be assessed against the pinned
[options](https://github.com/AeneasVerif/charon/blob/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/options.rs),
[MIR selection](https://github.com/AeneasVerif/charon/blob/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/bin/charon-driver/translate/get_mir.rs),
and [transforms](https://github.com/AeneasVerif/charon/tree/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/transform).
Optional transforms can change which obligations are explicit; adopting an
Aeneas preset without auditing it is not the configuration tested here.

## Next bounded increment

Prototype a ULLBC adapter for a checked increment and an owned restoring guard
through the ordinary Click engine. Verify true postconditions; reject false
values, possible overflow, forged authority, and duplicate cleanup at their
documented boundaries. Exercise verification, profiling, audit, and expansion,
including checking the expanded proof. Then compose the guard with a borrowed
loop and add compact-array/control-flow scaling checks. Only promote the adapter
after those results and phase/source locks are reviewable. Successful extraction
of the checksum is a reason to run this experiment, not to skip it.

## Reproduction

Build the pinned external tool without changing Click's default compiler:

```bash
git clone https://github.com/AeneasVerif/charon.git /tmp/click-charon
git -C /tmp/click-charon checkout 5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component rust-src
charon_sysroot=$(rustc +nightly-2026-09-17 --print sysroot)
export LIBRARY_PATH="$charon_sysroot/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export CARGO_PROFILE_DEV_DEBUG=0
cargo +nightly-2026-09-17 build --locked --manifest-path /tmp/click-charon/charon/Cargo.toml --target-dir /tmp/click-charon-target --bin charon --bin charon-driver
python3 design/borrow-probes/charon_probe.py --charon /tmp/click-charon-target/debug/charon --output /tmp/click-charon-results
```

Use a fresh output directory. Each extractor invocation has a 45-second external
process containment bound; no invocation timed out in the recorded run. To
include the checksum probe, download the original `src/lib.rs` and `src/algo.rs`
at the manifest revision into one directory and pass `--adler2-dir DIRECTORY`.
The script checks both source hashes before extraction. Artifacts and logs are
external investigation outputs; the normal repository gate does not run Charon
or install this extra toolchain. No external tool source was patched for the
experiment.
