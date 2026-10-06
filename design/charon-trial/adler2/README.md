# Unchanged adler2 crate adapter trial

Run on 2026-10-06 against the native Charon backend. **The crate does not yet
pass through Click's checked adapter. No Adler-32 postcondition is verified.**

The two files in `src/` are byte-for-byte copies of adler2 2.0.1, revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`. Their hashes match the existing
[source manifest](../../rust-checksum-sources.json). The original 0BSD license
is included. Neither modules, derives, methods, operators, nor loops were edited.

## Observed pipeline

| Stage | Result |
| --- | --- |
| Source identity | Both original source hashes match |
| Selected extraction | Succeeds with edition 2021, `std`, and `adler2::adler32_slice` |
| Native MIR selection | Optimized MIR, precise drops, reconstructed fallible operations |
| Extracted computation | 15 bodies including glue; `compute` has 94 blocks |
| Production import | Rejects with `Charon trial requires exactly one locked source file` |
| Artifact and lock publication | Neither is published |
| Checked lowering and proof | Not reached |

The [result record](result.json) contains the exact compiler/extractor profile,
body shapes, and file identities. The selected extraction uses the production
MIR transforms, but its edition, feature, and root selection are **not supported
production configuration fields**. The production attempt instead uses its
fixed edition 2024, no feature flags, and all local items. These are distinct
experiments; successful selected extraction does not establish configuration
parity or successful adaptation.

Unlike the older elaborated-MIR extraction assessment, this run uses the
native adapter's optimized-MIR selection. Its smaller block count is not
evidence of checksum verification.

## Reproduce

Build Click and pinned Charon with the normal repository setup. Run the live
regression, which checks source hashes, invokes the real production refresh,
and requires rejection before publishing an artifact or lock:

```sh
export CLICK_CHARON="$PWD/target/charon/debug/charon"
cargo nextest run --test rust_import --run-ignored only \
  -E 'test(charon_adler2_crate_trial_rejects_unlocked_module_closure)'
```

To reproduce the selected extraction, create a fresh output directory and run:

```sh
trial_output=$(mktemp -d)
target/charon/debug/charon rustc \
  --ullbc --mir optimized --precise-drops \
  --reconstruct-fallible-operations --sysroot default \
  --opaque core --opaque alloc --opaque std --error-on-warnings \
  --start-from adler2::adler32_slice \
  --dest-file "$trial_output/adler2.ullbc" -- \
  "$PWD/design/charon-trial/adler2/src/lib.rs" \
  --crate-name adler2 --crate-type lib --edition 2021 \
  --target x86_64-unknown-linux-gnu \
  -Cpanic=abort -Coverflow-checks=on -Zmir-opt-level=0 \
  --cfg 'feature="std"'
```

## Next adapter boundary

First add an explicit, locked crate configuration: crate root, edition,
features, selected roots, and the complete compiler-observed source closure.
Changes to either module must invalidate a prepared import. Reject missing,
extra, changed, or escaping source inputs before publishing outputs.

Do not identify that closure by `crate_name` alone. This run also contains a
virtual `adler2` source from the standard library's dependencies, alongside the
two local target files. Its same-name crate is a different compilation unit.
Use compiler file/declaration ownership and paths, and lock dependencies
through the compiler/runtime identity rather than treating them as target files.

Next preserve qualified declaration identities for `algo::U32X4`, inherent
methods, and trait implementations. The checksum path reaches the concrete
`Default` constructor, `U32X4::from`, and its assignment operators. These
bodies require checked interpretation; accepting methods by their final name
or assuming the checksum result would bypass the trial's purpose.

Only after the original reachable computation adapts can sidecars establish
access bounds, no panic, byte preservation, termination, and the shared
Adler-32 specification described in the [checksum assessment](../../rust-checksum-assessment.md).

## Follow-up: locked crate inputs

Schema 4 provides the crate root, edition, features, selected roots, and
complete rustc dep-info closure. Earlier crate increments reached the concrete
`Default` constructor, then by-value `U32X4` operator operands, then scalar
constant initializers. The current
`charon_adler2_locked_crate_imports_compute_and_proves_constants` live
regression imports the complete original selection with Rust 2021 and `std`.
The separate `charon_adler2_unchanged_constructor_returns_initialized_state`
regression selects `Adler32::new`, imports its actual `Default` body, and
proves both functions return `a = 1`, `b = 0` using ordinary aggregate-return
contracts. False initialized-field claims are rejected. The result record
above remains the historical single-file trial.

Multi-module regressions prove separate same-named functions and an inherent
method call, including a false-claim negative. Changes to an unreachable
module invalidate the lock. Crate configuration changes, missing or extra
files, path escapes, and symlinks are rejected.

### Owned operator operand follow-up

Schema-4 `click-charon-crate-v3` imports by-value flat-record operator operands
and preserves compiler Copy/Move events through fresh kernel aggregate
parameter storage. At that version, the unchanged full-loop selection passed operator identity
registration and rejected local constant/global initializer bodies
(`MOD` and `CHUNK_SIZE`) before publishing an artifact or lock. The checksum
postcondition remains unproved. Constructor proofs continue to pass; synthetic
four-lane operator and ordinary-call regressions verify values, copy
independence, moves, and destructor-bearing parameters.

### Checked scalar constant follow-up

Schema-4 `click-charon-crate-v4` imports the unchanged full selection rooted at
`adler2::adler32_slice`, including `Adler32::compute`, and writes an artifact
and lock that load as prepared input. The local `MOD` and `CHUNK_SIZE`
initializers execute their imported scalar CFGs; checked contracts prove
65521 and 22208, and a false modulus claim is rejected. The vendored Rust
source remains unchanged. The earlier constant rejection boundary above is
resolved.

The checksum postcondition remains unproved. Next prove the imported four-lane
helpers and compose their contracts with nested chunks/remainder loop
invariants and the common checksum specification. Successful import alone
does not establish arithmetic safety or checksum correctness.
