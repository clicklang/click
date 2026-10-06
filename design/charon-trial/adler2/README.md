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
profiling, auditing, and expanded certificates must agree. These tool rechecks
run in the nightly suite; direct verification and rejection tests stay in the
ordinary gate.

## Lane batch arithmetic

The [bounds library](bounds.click) checks the mathematical ceilings proposed
for the lane-loop invariants after `n` four-byte vectors since the last
reduction:

```text
A(n) = 65520 + 255*n
B(n) = 65520 + 65520*n + 255*n*(n+1)/2
```

Checked product and truncating-division certificates establish the triangular
term's bound for every `n` in the batch range. At `n = 5552`, the ceilings are
`A = 1481280` and `B = 4294690200`; the latter leaves 277095 below `u32::MAX`.
At `n = 5553`, `B = 4296171735` exceeds u32. Initial ceilings cover reduced
lanes, and a byte of at most 255 preserves both successor bounds:
`a + byte <= A(n+1)` and `b + (a + byte) <= B(n+1)`. The triangular
successor identity and `B(n+1) = B(n) + A(n+1)` are checked with bounded
polynomial and nonnegative quotient-shift certificates. Given the
proposed `A(n)` and `B(n)` bounds and `n < 5552`, the next two additions remain
nonnegative and below the full-batch ceilings. The range is per batch; it
imposes no bound on the total number of batches in an input.

The native lane-step lemmas now compose those ceilings with unsigned Integer
observations to establish the exact widened `int64` addition guards used by
`U32X4::add_assign`. Checked no-wrap bridges prove that the updated native A
and B lanes have the mathematical sum values and satisfy their successor
ceilings. In B's update, the operand is the newly updated native A lane.

These are checked arithmetic implications. They do not yet establish the
lane bounds over the original iterator states or prove checksum correctness. The tests check
the bounds alongside the actual helper contracts in one prepared environment,
and reject a larger batch, missing bounds, false endpoints, altered product
or quotient certificates, altered recurrence coefficients, reversed quotient-shift
guards, and false A- or B-invariant steps.

## Index derived from iterator state

The [iterator bounds library](iterator-bounds.click) observes the existing
signed remaining-byte state as
`N(total, remaining) = truncating_quotient(to_integer(total) - to_integer(remaining), 4)`.
For a batch of at most 22208 bytes, with `0 <= remaining <= total`, it proves
`0 <= N <= 5552`. If at least four bytes remain, `N <= 5551`, the native
`remaining - 4` operation is defined, and consuming four bytes advances N by
exactly one. No processed-count local is introduced.

The native lane-step lemmas now compose with this derived index. Under the
A/B bounds at N and the byte bound, both addition guards hold and the updated
native lane observations satisfy the A/B ceilings at
`N(total, remaining - 4)`. Initial, empty, short-tail, small exact-multiple,
and final full-batch indices have checked endpoints. The library has 14 theorem
groups with 30 checked conclusions; verification, profiling, auditing, and
expansion recheck them alongside the existing arithmetic dependencies.

These implications match the adapter's stored remaining-byte state and
four-byte `next` transition. They do not yet prove that the original nested
loops establish and maintain the numeric bounds, lane bounds, and memory views.
Full checksum correctness and whole-loop panic freedom remain unproved.

Integer equality evidence now works in either orientation for explicit theorem
applications and fact transport, including observations of native values and
entry snapshots. This repairs the proof interface used to connect the derived
index to iterator transitions; it adds no new loop invariant or checksum claim.


## Reproduce

Build Click and pinned Charon with the normal repository setup. The frozen
artifact verifies without extracting again:

```sh
target/debug/click verify design/charon-trial/adler2/helpers.click
target/debug/click verify design/charon-trial/adler2/bounds.click
target/debug/click verify design/charon-trial/adler2/iterator-bounds.click
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

Establish and preserve the lane invariants over the original chunks/remainder
iterator states using the derived index, checked A/B recurrences, and native
u32 observation bridges. Then use the helper contracts and byte accounting
to connect the original computation to the common specification in the [checksum assessment](../../rust-checksum-assessment.md).
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
