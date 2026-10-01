# Rust checksum source assessment

This assessment pins the existing Adler-32 implementations selected by
[the Rust roadmap](../issues/rust-support.md). It does not claim that Click
verifies either library. The scalar checkpoint supports `u8` and `u32`
arithmetic and bounded byte slices/indexing; wider integers, iterators, and crate support
follow from the actual
reachable source, rather than from a replacement checksum implementation.

## Immutable inputs and configuration

The companion [source manifest](rust-checksum-sources.json) records revisions
and SHA-256 hashes of the inspected files.

| Library | Immutable revision | Selected entry points |
| --- | --- | --- |
| zlib 1.3.1 | `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` | `adler32_z`, plus its `adler32` wrapper |
| adler2 2.0.1 | `89a031a0f42eeff31c70dc598b398cbf31f1680f` | `adler32_slice`; `Adler32::from_checksum`, `write_slice`, `checksum` |

The zlib release tag resolves to that commit. The Rust commit comes from
the published crate's `.cargo_vcs_info.json`; its two checksum source files
match the repository files byte for byte. Source links:
[zlib adler32.c](https://github.com/madler/zlib/blob/51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf/adler32.c),
[adler2 lib.rs](https://github.com/oyvindln/adler2/blob/89a031a0f42eeff31c70dc598b398cbf31f1680f/src/lib.rs),
[adler2 algo.rs](https://github.com/oyvindln/adler2/blob/89a031a0f42eeff31c70dc598b398cbf31f1680f/src/algo.rs).

The intended common verification target is `x86_64-unknown-linux-gnu`, with
eight-bit bytes, 32-bit C `unsigned int`, and 64-bit pointers, `unsigned long`,
and `size_t`. Keep zlib's normal remainder path: `NO_DIVIDE` and `Z_SOLO` are
unset. Do not rewrite its macro-unrolled loops or normalize its C source.
Compiler and header identities must enter the eventual Click input lock.

Keep adler2's declared Rust 2021 edition and default `std` feature. There
are no ordinary third-party dependencies for this configuration. The optional
`rustc-dep-of-std` feature is off; tests and benchmarks are not verification
roots. Use Click's pinned `nightly-2026-06-16`, overflow checks enabled,
panic abort, and MIR optimization level zero. The current exporter fixes Rust
2024 and one source file, so edition, features, crate roots, and all reachable
module bytes must become explicit locked inputs before importing this crate.

These are selected paths and a selected build configuration. The `BufRead`
adapter, zlib compression, alternate `NO_DIVIDE` code, and checksum-combine
APIs are outside this demonstration.

## Reachable computation

C calls `adler32` -> `adler32_z`, or enters `adler32_z` directly. Its arithmetic
splits the seed into two 16-bit components, handles lengths 1 and below 16,
then processes 5,552-byte blocks through `DO16` macro expansions. It uses
`while`, `do ... while`, decrement conditions, post-incremented byte pointers,
unsigned arithmetic, remainder, shifts, and bitwise packing. These are
existing C vocabulary; source import and proof coverage still need to be
demonstrated for the unchanged translation unit and selected configuration.
Unsupported declarations elsewhere in the same file may require selected-root
extraction, not deletion from the original file.

Rust's one-shot path is:

```text
adler32_slice
  Adler32::new -> Default::default
  Adler32::write_slice -> Adler32::compute
    U32X4::from
    U32X4::add_assign / rem_assign / mul_assign
    slice length, split_at, chunks_exact, remainder, iter
  Adler32::checksum
```

The incremental path starts with `Adler32::from_checksum`, then uses
`write_slice` and `checksum`. `compute` splits off the final zero to three
bytes and processes four independent lanes in chunks of 22,208 bytes
(`5552 * 4`). It combines the lane sums with weighted corrections, then
processes the short tail. This is a scalar fixed-array implementation of a
parallel checksum identity; the proof must establish that identity rather
than pretend the implementation is the textbook serial loop.

## Rust gaps exposed by these sources

| Source construct | Required checked interpretation |
| --- | --- |
| `u8`, `u16`, `u32`, `usize` | Target-sized types, loads/stores, unsigned comparisons and arithmetic |
| `u32::from`, `as`, `%`, `<<`, `|` | Resolved conversion calls, widening/truncation, remainder and bitwise rules |
| `&[u8]`, `.len()`, indexing, `split_at` | Address plus length, initialized byte views, bounds and partition checks |
| `[u32; 4]`, tuple struct `U32X4` | Fixed arrays, construction, copies and indexed field updates |
| `+=`, `%=`, `*=` on `U32X4` | Compiler-resolved concrete operator implementations and checked contracts |
| `for`, nested loops, `.chunks_exact()`, `.remainder()`, `.iter()` | Iterator state, yielded subranges, progress and existing loop invariants |
| `mod`, `use`, inherent methods, `Default`, `Copy` derives | Crate-aware extraction and selected concrete reachable definitions |

The current exporter accepts `i32`, booleans, selected structs/references,
branches, and direct local calls. It does not import this library. Invoking it
on unchanged `src/lib.rs` fails promptly with the documented one-file boundary
diagnostic about modules, macros, imports, and attributes. Do not strip those
constructs from adler2 to turn that rejection into an apparent success.

Support the reachable concrete instantiations rather than promising arbitrary
traits or generics. Slice and iterator operations need either checked lowering
or individually named library contracts in the trust boundary. The checksum
and `U32X4` arithmetic bodies themselves must be verified, not assumed.

## Shared specification and proof boundary

For prime `P = 65521`, a canonical initial state `0 <= a0,b0 < P`, and a byte
sequence `x`:

```text
a(i+1) = (a(i) + x[i]) mod P
b(i+1) = (b(i) + a(i+1)) mod P
checksum(x, a0, b0) = a(len(x)) | (b(len(x)) << 16)
```

One-shot comparison uses `(a0,b0) = (1,0)`. Incremental comparison uses the
same canonical state on both sides and proves processing concatenated input
agrees with successive updates. Do not equate arbitrary packed seeds or
zlib's null-buffer reset behavior with a Rust slice. C requires a non-null,
initialized, readable byte range for the selected comparison, including a
valid non-null empty-range representation when length is zero. Rust permits
an empty slice with its normal validity conditions.

Both proofs preserve input bytes, establish access bounds and termination,
and exclude Rust panics. In particular, the deferred-reduction proof must
bound each intermediate Rust `u32` lane and the combined accumulators. The C
accumulators are LP64 `unsigned long`; matching outputs does not justify
silently giving the Rust operations that wider type.

Read-only slice authority should use existing Click `views` of the input
byte range; mutable accumulator fields use `owns`. Slice length and validity
remain separate from allocation/deallocation authority. Existing unsigned
types, memory ranges and loop invariants are the first choice. A 64-bit `usize`
length must not be silently truncated to fit a narrower memory-range model;
that representation needs either full target-width support or explicit checked
bounds in an intermediate subset. This assessment
does not establish a need for new public Click syntax.

## Reviewable implementation increments

The shared field-borrow blocker was repaired in
[PR #29](https://github.com/clicklang/click/pull/29). The nested guard proves the
child's write of 42 and rejects a stale result of 1, with checked expansion.
The subsequent scalar checkpoint covers `u8`/`u32`, casts, unsigned comparisons,
remainder, shifts, bitwise operations, and checked panic obligations. `u16`
and general target-sized `usize` arithmetic remain outstanding. Byte slices
now support `.len()`, indexed reads/writes, local reborrows and direct calls;
variable-length memory contracts currently require length at most `INT32_MAX`.
Slice metadata and index checks retain the target's full 64-bit width.

1. Add `u8`, `u16`, `u32`, and target-sized `usize` to the Rust artifact and
   direct lowering, together with required casts, unsigned comparisons,
   remainder, shifts, and bitwise operations. Keep overflow, divide-by-zero,
   and shift obligations checked. A small Rust arithmetic regression should
   verify a true result and reject a false one, overflow, and invalid shifts.
   This is frontend evidence, not an existing-library verification claim.
2. Add byte slices and fixed arrays, bounds-checked indexing, and slice-length
   access using existing memory resources. Cover unchanged input, out-of-bounds
   rejection, and mutable/shared access separation.
3. Lock crate configuration and source closure, resolve concrete methods and
   operators, and model the selected slice/iterator operations. Add structured
   loops with sidecar invariants and progress checks, including nested chunks.
4. Prove the serial specification, chunk accumulation bounds and four-lane
   identity; verify the two pinned computations unchanged. Reject a false
   checksum claim through Click and run ordinary verification, audit, profile,
   expansion, and re-verification for the completed example.

Each increment gets its own coherent green checkpoint. Shared checker or
expansion failures take priority over the next increment. Full arbitrary-input
verification remains the milestone; a length-limited proof may be intermediate
evidence only if its bound is explicit.

## Assessment evidence

- Original adler2 source compiled with the pinned compiler, Rust 2021,
  `std`, overflow checks and panic abort for the selected Linux target
  (metadata emission). Its file hashes match the immutable repository sources.
- Original zlib checksum source passed a host Clang syntax check with its
  pinned headers. The host macro dump confirmed LP64 widths and that
  `NO_DIVIDE` and `Z_SOLO` were absent. This is not yet a Linux Click import.
- 126 host differential checks compared the unchanged implementations with canonical
  seeds and non-null byte buffers around lengths 1, 4, 16, 5,552 and 22,208.
  They are supplementary runtime evidence, not functional verification.
- The current Rust exporter rejected the original crate promptly at its known
  source boundary. No implementation source was changed for this assessment.
