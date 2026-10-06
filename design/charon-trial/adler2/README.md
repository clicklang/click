# Unchanged adler2 crate adapter trial

Click imports the complete selection rooted at `adler2::adler32_slice` and
proves the four-lane helper bodies. **The Adler-32 checksum postcondition
remains unproved.**

The two files in `src/` are byte-for-byte copies of adler2 2.0.1, revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`. Their hashes match the
[source manifest](../../rust-checksum-sources.json). The original 0BSD license
is included. Neither modules, derives, methods, operators, nor loops were edited.

## Current checked boundary

Schema 4 locks the Rust-2021 crate root, `std` feature, selected entry point,
and complete rustc dep-info closure. Both module files enter the prepared
identity. Missing, extra, changed, escaping, or symlinked inputs are rejected.
Qualified declaration identities distinguish module functions, inherent
methods, and concrete assignment-operator implementations.

The `click-charon-crate-v4` adapter imports the original reachable computation,
including `Adler32::compute`. Constructor regressions prove that the actual
`Adler32::default` and `Adler32::new` bodies return `a = 1`, `b = 0`. Scalar
initializer contracts prove `MOD = 65521` and `CHUNK_SIZE = 22208` by executing
their imported CFGs.

The [helper sidecar](helpers.click) uses the [locked configuration](helpers.click.import.json)
and native Charon artifact to prove every lane of these original helpers:

| Body | Contract |
| --- | --- |
| `U32X4::from` | At least four bytes and a shared view of the first four; each returned lane equals its corresponding input byte |
| `AddAssign<Self>` | Each widened lane sum fits u32; each output lane equals its old value plus the corresponding by-value operand |
| `RemAssign<u32>` | Nonzero divisor; each output lane equals its old value modulo the divisor |
| `MulAssign<u32>` | Zero multiplier or each lane fits the quotient bound; each output lane equals its old value times the multiplier |

Mutating helpers require ownership of all four receiver lanes. Addition uses
`(int64)` contract casts to express the exact Rust overflow guard; it permits
the full safe u32 domain. Multiplication's disjunction includes a zero multiplier
without evaluating division by zero. These proofs establish the access and
panic prerequisites in the helper bodies, conditional on their contracts.
They do not establish that the checksum loops satisfy those contracts.

Frozen and live regressions check the original source hashes, prove all four
helpers, and reject false lane claims, short reads, missing safety guards,
wrapping addition bounds, and mutation under a shared view. CLI verification,
profiling, auditing, and expanded certificates must agree.

## Reproduce

Build Click and pinned Charon with the normal repository setup. The frozen
artifact verifies without extracting again:

```sh
target/debug/click verify design/charon-trial/adler2/helpers.click
```

Refresh the entire selected crate through the production adapter:

```sh
target/debug/click import lock design/charon-trial/adler2/helpers.click
```

The configured exporter path is relative to this directory. Run the focused
live regression to refresh a private copy and reprove the original helper bodies:

```sh
export CLICK_CHARON="$PWD/target/charon/debug/charon"
cargo nextest run --test rust_import --run-ignored only \
  -E 'test(charon_adler2_helpers_live_refresh_proves_original_bodies)'
```

## Remaining proof work

Compose the helper contracts with the nested chunks/remainder loop invariants,
including lane bounds and byte accounting, then connect the original computation
to the common specification in the [checksum assessment](../../rust-checksum-assessment.md).
Successful import and helper proofs alone do not establish checksum correctness
or whole-loop panic freedom.

## Historical trial

The [result record](result.json) preserves the initial 2026-10-06 single-file
trial. Selected native extraction succeeded, but production schema 3 rejected
the two-file crate before publishing an artifact or lock. Schema 4 resolved
that input boundary; subsequent increments added checked constructors, by-value
operator operands, and scalar constant initializers. The historical result's
rejection is not the current adapter status. Schema-3 configurations retain
their single-file interpretation.
