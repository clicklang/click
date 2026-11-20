# Unchanged adler2 crate adapter trial

> **Status.** The lane helpers and the empty, one-, two-, and three-byte
> `compute` proofs check against the locked crate on the current verifier.
> The four-byte boundary also checks the original vector path. These proofs
> read the real `ChunksExact` fields and use source statement selectors for
> the arithmetic. The small-batch and general proofs below still refer to
> the removed iterator model and generated operand locals. The public and
> client proofs depend on the general computation. Whole-claim expansion
> of the one- and four-byte computations currently stops at an internal
> value without a proof spelling.

The sections below describe the original proof structure.

Click imports the complete selection rooted at `adler2::adler32_slice` and
proves the four-lane helper bodies and the unchanged general computation.
For every input length from any canonical initial state, `Adler32::compute`
terminates, preserves input bytes, and stores both fields equal to the shared
`uint64` checksum specification (`adler_spec_a_u64`/`adler_spec_b_u64` at
`bytes.len()`) on the entry state. The proof follows actual native remaining
counts, `uint64` iterator cursors and shared input views through all original
loops, reductions and final stores; no length bound is required. The unchanged
`adler32_slice` entry point composes the checked constructor, general update
and getter and returns the specified packed checksum for every length. A locked
real Rust client proves two consecutive updates equal the full-input checksum
for every valid split, preserving all bytes. A second client proves the same
result after saving the prefix checksum and restoring a fresh receiver before
continuing.

Batch-local counts (a full batch is 22,208 bytes) are observed as `int32`
through the bound library ([`bounded-count.click`](bounded-count.click)), and
the per-step lane and scalar lemmas state the int32 specification. Each
step applies them at offset 0 of the input at the `uint64` cursor and joins the
result to the `uint64` prefix through the
[bridge](../adler32-spec-bridge.click) and `adler_spec_a/b_concat_u64`.

Every public and client contract, here and in the [zlib trial](../zlib/README.md),
states its result over the full-width [`uint64` specification](../adler32-spec-u64.click)
with no length limit. The [int32 specification](../adler32-spec.click) and the
bridge remain on purpose as the per-batch computation layer: a batch or tail
never exceeds 22,208 bytes, its sums are proved at that constant width, and
the bridge joins each result to the full-width prefix.

The function contracts use Rust syntax (`docs/reference/rust.md`,
"Signatures in Rust syntax"): `fn` signatures, `impl` blocks, paths such as
`adler2::algo::U32X4`, `bytes.len()` and `p.f`. Proofs use `have P;` and
`by T(args);` for single steps. The standalone theorem libraries keep Click's
numeric types and casts because the same lemmas also check C proofs.
Rust sources require this function spelling; C-shaped signatures and reference
fields written with `->` are refused.

The two files in `src/` of
[`../../vendor/adler2-2.0.1`](../../vendor/adler2-2.0.1), outside the Click
project, are byte-for-byte copies of adler2 2.0.1, revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`, at their upstream paths. The
client crates `incremental.rs` and `resumed.rs` include them with
`#[path = "../../vendor/adler2-2.0.1/src/lib.rs"]`. Their hashes match the
[source manifest](../../../rust-checksum-sources.json). The original 0BSD license
is included. Neither modules, derives, methods, operators, nor loops were edited.

## Installed demonstration

The [C/Rust checksum demonstration](../checksum-correspondence.md#reproduce)
copies the locked fixtures and assembles these canonical proof fragments into
ordinary CLI sidecars. Its installed workflow checks the complete computation,
public API, two-update client, saved-state client, C producers and correspondence
outside the checkout, without a compiler. The fragment files below are shared
proof inputs; files such as `public-general.click` need their helper declarations
and are not standalone CLI entries.

## Current checked boundary

The crate, source closure, selected entry points and semantic profile are locked
by [the project configuration](../click.project.json) and its import lock.
The original `lib.rs` and `algo.rs` stay byte-for-byte pinned; clients add their
own source without changing either library file. The adapter imports original
helper bodies, checked constructors/getter, resolved assignment operators,
ULLBC control flow and drop behavior. Trusted iterator/library models and the
compiler/adapter boundary remain those of the
[native adapter](../../../charon-trial/README.md).

The general proof covers every valid slice length and canonical entry seeds
`a,b < 65521`, all 22,208-byte batches, the aligned vector remainder, scalar
tail, reductions and final stores. It follows actual iterator state, proves
termination and input-byte preservation, and retains both checksum residues
against the full-width specification. The int32 layer is deliberately local
to bounded batches; it imposes no overall length cap. No assumed checksum
summary or generated processed counter supplies the induction.

## Proof dependencies

| Claim | Checked producer/dependencies |
| --- | --- |
| Original helpers and native lane arithmetic | [helpers.click](helpers.click), [bounds.click](bounds.click), [recombination.click](recombination.click), [four-byte-spec.click](four-byte-spec.click) |
| Full-width progress and bounded batch steps | [general-partition.click](general-partition.click), [count-bridge.click](count-bridge.click), [batch-prefix.click](batch-prefix.click), [remainder-prefix.click](remainder-prefix.click), [tail-bounds.click](tail-bounds.click) |
| Original general computation | [general-compute.click](general-compute.click), assembled with its helper bodies and lemmas by the demonstration/test harness |
| Constructors, getter and public entry points | [public-constructors.click](public-constructors.click), [checksum.click](checksum.click), [public-general.click](public-general.click) |
| Real two-update and saved-state clients | [incremental.click](incremental.click), [restoration.click](restoration.click), [resumed.click](resumed.click) |
| Native C/Rust return and reset correspondence | [correspondence.click](correspondence.click), under matched state/bytes and each producer's own authority requirements |

The [scoped demonstration](../checksum-correspondence.md) gives complete
producer commands, installed/offline reproduction and exact matched-input,
canonical-seed and nonnull C boundaries. Importing a function contract alone
does not check its body. The prepared producer sidecars include the bodies;
correspondence composes their results and does not verify an FFI boundary.

## Reproduce

Build Click and pinned Charon with the normal repository setup. The frozen
artifact verifies without extracting again:

```sh
target/debug/click verify design/adler32/project/adler2/helpers.click
target/debug/click verify design/adler32/project/adler2/bounds.click
target/debug/click verify design/adler32/project/adler2/iterator-bounds.click
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

Refresh every unit of the project through the production adapter:

```sh
target/debug/click capture design/adler32/project/adler2/helpers.click
```

`CLICK_CHARON` selects a source-built Charon. Run the focused live regression to refresh a private copy and reprove the original helper bodies:

```sh
export CLICK_CHARON="$PWD/target/charon/debug/charon"
cargo nextest run --test rust_import --run-ignored only \
  -E 'test(charon_adler2_helpers_live_refresh_proves_original_bodies)'
```

## Tool limits and historical evidence

The recorded full-computation smart audits exhausted the standard ten-minute
run bound before completing a site. That is an audit-tool limitation and
supplies no proof verdict; ordinary verification success does not establish a
successful full audit. Focused byte observations and helper checks are separate
evidence. Reproduce the affected audit before changing tooling or budgets.

The [original checkpoint ledger](https://github.com/clicklang/click/blob/2175760b9/design/adler32/project/adler2/README.md)
and [initial result](result.json) preserve extraction and partial-proof history.
Statements there that general checksum induction, full-width lengths or
incremental processing remained unproved were superseded by the producers
above. The source fragments, locked inputs and distinct negative controls remain.
