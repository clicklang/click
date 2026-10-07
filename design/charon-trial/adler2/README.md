# Unchanged adler2 crate adapter trial

Click imports the complete selection rooted at `adler2::adler32_slice` and
proves the four-lane helper bodies and the original computation on empty input
from `a = 1`, `b = 0`. **The general Adler-32 checksum postcondition remains
unproved.**

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
| `U32X4::from` | At least four bytes and a shared view of the first four; each returned lane equals its corresponding input byte and is at most 255; each unsigned Integer observation lies in `0..255` |
| `AddAssign<Self>` | Each Integer lane sum fits u32; each output lane equals its old value plus the corresponding by-value operand, with exact Integer sum and nonnegative observation |
| `RemAssign<u32>` | Nonzero divisor; each output lane equals its old value modulo the divisor, is below the divisor, and has an Integer observation in `0..divisor-1` |
| `MulAssign<u32>` | Zero multiplier or each lane fits the quotient bound; each output lane equals its old value times the multiplier, with exact Integer product and observation in `0..4294967295` |

Mutating helpers require ownership of all four receiver lanes. Addition accepts
Integer sum bounds and derives the widened `(int64)` Rust overflow guards;
it permits the full safe u32 domain. Multiplication's disjunction includes a zero multiplier
without evaluating division by zero. These proofs establish the access and
panic prerequisites in the helper bodies, conditional on their contracts.
They do not establish that the checksum loops satisfy those contracts.

The constructor also exports `0 <= to_integer(lane) <= 255` for each lane.
Its proof applies checked unsigned-order bridges to the actual returned
fields, making the byte bounds usable by the Integer lane-step lemmas. The
bridges retain the full u32 range; signed reinterpretation would be unsound
for accumulated B lanes above the sign bit.

The remainder helper exports the strict native and Integer divisor bounds
for all four lanes, along with nonnegative Integer observations. Its original
`%=` body proves those guarantees for every nonzero u32 divisor. Specializing
the call to `MOD = 65521` yields the `0..65520` range needed to reset both
lane ceilings before a new batch. This does not establish the reset or
preservation over the original outer loop yet.

The multiplication helper also exports the exact Integer product for each lane.
`uint32_mul_to_integer` uses the original native quotient guard, including its
zero-factor branch, to justify the non-wrapping observation. This lets caller
proofs carry numeric lane ceilings through the original `*=` body: for example,
a reduced lane at most 65520, multiplied by four, has an Integer observation at
most 262080. The theorem covers the full unsigned range; defined wrapping
multiplication alone cannot justify an exact mathematical product. Kernel
regressions check unsigned boundary values and both sides of the last safe
quotient. Helper regressions reject false products/bounds and missing guards
independently for every lane. The four-byte caller proof below uses these bridges.

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
observations to establish the widened `int64` addition guards in the original
`U32X4::add_assign` body. Its sidecar now accepts the corresponding Integer
no-wrap bounds and exports exact Integer sums and nonnegative observations
for all four updated lanes. The checked addition bridge discharges the native
overflow guards without changing the original body. Checked no-wrap bridges
prove that the updated native A and B lanes have the mathematical sum values and satisfy their successor
ceilings. In B's update, the operand is the newly updated native A lane.

These are checked arithmetic implications. They do not yet establish the
lane bounds over the original iterator states or prove checksum correctness. The tests check
the bounds alongside the actual helper contracts in one prepared environment,
and reject a larger batch, missing bounds, false endpoints, altered product
or quotient certificates, altered recurrence coefficients, reversed quotient-shift
guards, and false A- or B-invariant steps.

## Recombination arithmetic

The [recombination library](recombination.click) proves exact Integer values
and overflow guards for the original expressions `b + (MOD - a)`,
`b + (MOD - a) * 2`, and `b + (MOD - a) * 3`. Given a reduced A lane below
65521 and a B lane already multiplied by four with observation at most 262080,
the respective ceilings are 327601, 393122, and 458643.

The checked `uint32_subtract_to_integer` rule requires the native unsigned
no-underflow guard. It relates `MOD - a` to `65521 - to_integer(a)` across the
full unsigned domain. Defined unsigned subtraction alone permits wrapping.
Regressions check the bridge's actual machine guard and observation against an
independent boundary model, executed C subtraction, expanded certificates,
missing bounds, and false lane weights or ceilings.

These are conditional arithmetic proofs checked alongside the original helper
contracts. They do not establish the premises at each original recombination
site or prove the complete four-byte checksum by themselves. The four-byte
caller proof below supplies those premises; general initial states and
preservation over larger nonempty vector batches remain open.

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


## Original empty-input computation

The same [locked sidecar](helpers.click) now checks the unchanged
`Adler32::compute` body with an empty input and initial state `a = 1`, `b = 0`.
It requires ownership of both state fields and a shared empty input view,
and proves both output fields: `a = 1`, `b = 0`. All four helper contracts and
both constant getter bodies are verified in the same file.

The proof checks the original scalar addition and modulo, lane recombination,
ordered shared array iterations, final modulo results, and narrowing stores.
For this input the recombined B lanes are `0`, `65521`, `131042`, `196563`;
their sum is `393126 = 6 * MOD`, which reduces to zero. Snapshot equations and
explicit rewrites retain the actual operand values. The proof names a few
adapter capture locals to cite original call results directly; it introduces
no source variables, processed counter, assumed loop invariant, or proof hole.
These low-level names are tied to the frozen import and must recheck after
adapter changes.

The complete boundary proof and false-output rejections take longer than a
few seconds and run in the nightly suite. Missing empty-input, scalar B, and
ownership prerequisites are ordinary regressions. Nonempty chunk/tail
preservation, arbitrary initial-state preservation, and the general checksum
contract remain later work.

## Original single-byte computation

[single-byte-compute.click](single-byte-compute.click) checks the unchanged
`Adler32::compute` body with one arbitrary byte from the constructor state
`a = 1`, `b = 0`. It owns both state fields, borrows the input, and proves that
the input byte is preserved. The final field observations are checked in the
original modulo form: `a = (1 + byte) % MOD` and
`b = (6 * MOD + 1 + byte) % MOD`. For a byte in `0..=255`, these are the
single-byte checksum values `a = b = 1 + byte`.

The proof follows the stored serial iterator, identifies its read with the
original byte, bounds both additions, and checks the final modulo and `u16`
stores. The kernel cast-identity rule recognizes both canonical nested casts
and the exact unsigned masks used by byte readback, with explicit destination
range bounds. No Rust source, extraction artifact, lock, or import profile changes.

This file is a contract fragment. Function-contract imports between Click
sidecars are not admitted yet, so the fixture harness combines it with the
canonical helper and constant-getter contracts from `helpers.click` and
checks all seven bodies. This preserves the empty-input sidecar and avoids
duplicate helper interfaces. The full positive proof, false checksum and
byte-preservation claims, and verify/profile/audit/expansion rechecks are
nightly tests; missing length/view and empty-input rejections are ordinary tests.

## Original two- and three-byte serial tails

[two-byte-compute.click](two-byte-compute.click) and
[three-byte-compute.click](three-byte-compute.click) extend the constructor-state
proof to arbitrary inputs of length two and three. Every original serial read
is identified with its input position. After read `j`, the stored cursor is
`old(bytes) + j` and its remaining count is `length - j`; no processed-count
local or assumed loop invariant is introduced.

Each iteration proves the native recurrence `A_j = A_(j-1) + byte_(j-1)` and
`B_j = B_(j-1) + A_j`, starting from `A_0 = 1`, `B_0 = 6 * MOD` after the
unchanged lane recombination. The checked upper bounds for A are 256, 511,
and 766, and for B are 393382, 393893, and 394659. These discharge both
original overflow checks on each pass. The final field observations equal
the native `A_length % MOD` and `B_length % MOD` expressions through the
original `u16` stores, and every input byte is preserved.

The same fixture assembly checks the canonical helper/getter bodies alongside
each computation fragment. Nightly regressions reject false A/B results,
changes to each preserved byte, swapped byte weights in B, and repeated reads
of a preceding byte. Verify/profile/audit/expansion recheck both contracts.
Missing length/view, wrong extent, and wrong constructor-state premises have
ordinary rejection checks. Rust source, extraction artifacts, locks, and the
import profile remain unchanged.

## Reproduce

Build Click and pinned Charon with the normal repository setup. The frozen
artifact verifies without extracting again:

```sh
target/debug/click verify design/charon-trial/adler2/helpers.click
target/debug/click verify design/charon-trial/adler2/bounds.click
target/debug/click verify design/charon-trial/adler2/iterator-bounds.click
```

Check the single-byte fragment against the same locked native body and shared
contracts, including proof-tool rechecks:

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_single_byte_compute)'
```

Check both new serial-tail fragments and their negative/tool regressions:

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_short_tail_compute) | test(charon_adler2_two_byte_compute) | test(charon_adler2_three_byte_compute)'
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

The first nonempty vector path also exercises a by-value copy of `a_vec` after
its checked addition helper. Initialized local arrays now copy from the current
memory snapshot when that helper has discarded cached lane values. The reduced
[copy-after-call regression](../copy-after-call/README.md) checks this prerequisite
and independence from subsequent source writes.

The [four-byte computation contract](four-byte-compute.click) now checks the
original constructor-state vector path through all three weighted lane updates,
both ordered lane summation loops, the empty serial tail, and the final modulo
and u16 stores. It preserves all four input bytes and gives exact native checksum
expressions modulo 65521, retaining the original MOD offsets in B. The helper
and recombination lemma bodies are checked alongside this contract. No original
Rust, Charon artifact, import configuration, or lock changes are needed.

The proof tracks the stored iterator cursors and remaining lengths. Checked
native-to-Integer additions establish final scalar ceilings of 1021 and 397210;
the output casts are justified by the modulo range. Nightly regressions check
false outputs, byte ordering, repeated reads, and agreement between verification,
profiling, audit, expansion, and verification of the expanded contract.

With constructor-state inputs of lengths zero through four checked, next
establish and preserve the lane
invariants over the original chunks/remainder
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
