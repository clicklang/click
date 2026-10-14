# Checked C/Rust Adler-32 correspondence

The unchanged pinned zlib C implementation and adler2 Rust implementation
satisfy [one mathematical specification](../adler32-spec.click).
[correspondence.click](adler2/correspondence.click) derives native return-word
equality from their checked postconditions, matching initial state, length,
and entry bytes. This is a composition of separately checked programs;
it does not import a mixed C/Rust executable or prove an FFI boundary.

## Matched calls

Let `n` be a length from 0 through 2147483647, and let `A0` and `B0` each
be from 0 through 65520. Give C a seed whose decoded low/high 16-bit fields
are `A0`/`B0`, and Rust a receiver with those fields. The C buffer must be
nonnull. Each caller supplies the read authority required by its contract.
The buffers may be distinct allocations, provided their entry snapshots have
the same byte at every index `0 <= k < n`.

| Checked producer | Result observation |
| --- | --- |
| C [canonical.click](zlib/canonical.click) | `to_integer(c_result) == adler_spec_checksum(c_bytes, n, A0, B0)` |
| Rust [public-general.click](adler2/public-general.click), then [checksum.click](adler2/checksum.click) | `to_integer(rust_result) == adler_spec_checksum(rust_bytes, n, A0, B0)` |

`adler_c_rust_results` uses the checked specification's extensionality theorem
to identify these two mathematical checksums. `adler_result_widen` proves that
converting the Rust `uint32` word to the C LP64 `uint64` word preserves its
Integer observation. Checked uint64 injectivity then gives
`c_result == (uint64)rust_result`. The result premises come from the producers;
the correspondence theorem does not establish memory authority or execute them.

For the standard seed, take `A0=1`, `B0=0` and use Rust's checked
`adler32_slice`. For saved-state updates, the checked
[from_checksum](adler2/restoration.click) decodes all `uint32` words, but the
update proof requires both decoded fields to be canonical. The C seed may have
bits above bit 31: its original masking ignores them. Match the decoded fields,
not the full LP64 seed word.

## Incremental calls and reset

The actual [C two-call client](zlib/incremental.click) and
[Rust two-write client](adler2/incremental.click) independently produce the
whole-input checksum. Instantiate the same correspondence theorem with their
return words and whole-input entry snapshots. Both splits may range from zero
through the total length; their split positions need not be equal. The C
client requires both call pointers to be nonnull, including empty pieces.
Rust's [saved/restored client](adler2/resumed.click) has the same standard-seed
whole-input result observation.

C's [null reset](zlib/reset.click) returns `1` for any seed and any native
length other than `1`, with no buffer view. The unchanged one-byte fast path
precedes the null check, so `NULL,1` is excluded. Rust's checked
[new/default constructors](adler2/public-constructors.click) produce fields
`A=1,B=0`; the checked getter packs those as `1`.
`adler_c_rust_reset` connects these exact postconditions. An ordinary empty
nonnull update preserves the supplied state and is not a reset request.

## Reproduce

Run from the repository root with its pinned tools activated. The existing
prepared imports and locks bind source closures, extraction/compiler identity,
target layout, flags and supported models. The offline tests relocate those
fixtures and check dependency bodies; a standalone `click verify` selects
only the named file's proofs and treats imported contracts as assumptions.
For Rust fixture commands, set `CLICK_CHARON` to the pinned exporter from
`scripts/build-charon.sh` (and install its pinned compiler if needed):

```sh
export CLICK_CHARON="$(scripts/build-charon.sh)"
export RUST_MIN_STACK=8388608
```

The bounded normal regression checks correspondence bodies and rejects
missing byte matching, mismatched initial state, an incorrect result, and a
wrong constructor field:

```sh
cargo test --test compiler_import adler_c_rust_correspondence_requires_matched_inputs
cargo test --test compiler_import pinned_zlib_null_reset_is_independent_of_seed_and_nonunit_length
```

These individually selected nightly fixtures check producer bodies and
complete expansions. They are reproducible commands, not a request to run
the entire nightly suite:

```sh
cargo test --test compiler_import adler_c_rust_correspondence_expands_with_checked_dependencies -- --ignored
cargo test --test compiler_import pinned_zlib_canonical_seed_matches_checked_shared_specification_offline -- --ignored
cargo test --test rust_import charon_adler2_general_public_checksum_tools_check_all_original_bodies -- --ignored
cargo test --test compiler_import pinned_zlib_incremental_c_matches_checked_shared_specification_offline -- --ignored
cargo test --test rust_import charon_adler2_incremental_client_tools_check_all_original_bodies -- --ignored
cargo test --test rust_import charon_adler2_resumed_client_tools_check_all_original_bodies -- --ignored
```

The proof covers the original scalar, vector/block, NMAX batch and tail paths
under these contracts, together with termination and byte preservation.
Lengths beyond the common signed-index limit, noncanonical update state,
allocation lifetime and an FFI calling convention are outside this claim.
Compiler import and library trust boundaries remain those documented by the
[Rust trial](README.md) and [C fixture](zlib/README.md).
