# Experimental Rust imports

Click's first Rust frontend accepts a small safe, monomorphic subset of Rust
2024. It imports unchanged source through a repository-owned exporter using
pinned rustc typed HIR and drop-elaborated MIR after type checking and borrow
checking. The exporter writes a typed JSON artifact; Click lowers that artifact directly to the shared
kernel execution vocabulary. Verification uses the same sidecars, tactics,
certificates, and bounded engine as C and C++.

The working example is
[`examples/basic-rust/borrow.rs`](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.rs),
with its
[sidecar](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.click).
It covers a scalar branch, a mutable reference helper that writes through a
local reborrow and then reuses its parent, and a caller proving a struct field's
final value while preserving its other field. A shared field borrow remains
stable while the disjoint field is mutated.

## Reproduce the example

Run `scripts/setup-environment.sh` once. Its full mode installs
`nightly-2026-06-16` with `rustc-dev` and the `x86_64-unknown-linux-gnu` target. Click itself continues to use
its separately pinned stable toolchain. Build the exporter with
`scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
cargo run --bin click -- profile examples/basic-rust/borrow.click
cargo run --bin click -- audit examples/basic-rust/borrow.click
cargo run --bin click -- expand --claim update.contract --in-place examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

The import configuration selects one `.rs` file, the exporter executable,
and an artifact output. Refresh runs the compiler with a bounded process and
writes the artifact and input lock. Ordinary verification loads those files
without executing the compiler. Source, configuration, artifact, or profile
changes require refresh. The saved lock includes the compiler/exporter identity. After updating the
exporter, refresh existing imports. Configuration schema 2 is unchanged; the
typed artifact and lock now use schema 4.

## Supported semantics

The scalar slice supports `i32`, `u8`, `u32`, target-sized `usize`, booleans, unit returns, initialized scalar
and reference locals, branches, direct calls within the selected file,
references to `i32`, `u8`, and `u32`, and plain structs with those integers or reference fields, field
access, and local reborrowing of reference-backed places. Arithmetic supports addition,
subtraction, multiplication, division, remainder, bitwise operations, comparisons,
and boolean operations. Unsigned shifts support `u8`, `u32`, and `usize`; signed shifts
remain unsupported. Integer `as` casts preserve Rust truncation and bit
interpretation. Record
size, alignment, and field offsets come from rustc for the selected target;
Rust's default field order is not assumed.

The fixed profile is Rust 2024, compiler commit
`01dfd79246f1b2d5f146616deff08223a840a9ae`, target
`x86_64-unknown-linux-gnu`, overflow checks enabled, panic abort, and MIR optimization level zero. Click must
prove that arithmetic overflow does not occur. Compiler acceptance alone does
not prove a functional claim or panic freedom.

Unsigned arithmetic has Rust's checked semantics: addition, subtraction, and
multiplication require overflow freedom, and division/remainder require a
nonzero divisor. A shift count must be nonnegative and less than the left
operand's width (8, 32, or 64); shifting away high bits is allowed. Casts to `u8`
retain the low eight bits. Checks follow operand evaluation order and respect
`&&`/`||` short circuiting. Compound assignments use the same operations.
These obligations are checked during execution; C unsigned wrapping alone
cannot establish Rust panic freedom.

[`examples/rust-unsigned/arithmetic.rs`](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.rs)
is a synthetic scalar regression covering byte accumulation, multiplication,
modular reduction, shifts, packing, truncation, and unsigned comparison. Its
[sidecar](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.click)
uses ordinary Click contracts and tactics. Expansion can use the shared
`unsigned_sum_bound` arithmetic-certificate step for widened word bounds.
It does not establish checksum-library support;
iterator loops and crate extraction remain outstanding.

```sh
cargo run --bin click -- import lock examples/rust-unsigned/arithmetic.click
cargo run --bin click -- verify examples/rust-unsigned/arithmetic.click
```

## Byte slices and indexing

Shared `&[u8]` and mutable `&mut [u8]` parameters, local copies and reborrows,
builtin `.len()`, indexed reads and writes, and direct slice calls are supported.
Slice references lower to paired parameters: `bytes: &[u8]` becomes
`const uint8* bytes, uint64 bytes_len`; a mutable slice uses `uint8*`.
The generated `<parameter>_len` name must not collide with another parameter.
On the pinned target, `usize` is a 64-bit unsigned value, including lengths,
index literals, comparisons, casts, returns, and general scalar arithmetic.
Addition, subtraction, and multiplication require checked overflow freedom at
the full 64-bit width; division/remainder require a nonzero divisor. Bitwise
operations, checked shifts, and scalar compound assignments are supported.
Casts to `u32`/`i32` retain the low 32 bits, casts to `u8` retain the low eight
bits, and `i32 as usize` sign-extends before interpreting the bits as unsigned.
See [`examples/rust-usize`](https://github.com/clicklang/click/tree/master/examples/rust-usize)
for contracts over arithmetic, casts, computed indices, and length increments.

Every index checks `index < length` at the full target width before address
formation. Shared reads require `views`; writes require `owns`. Local slice
copies and calls preserve both pointer and length. The compiler checks borrow
legality; Click checks memory authority and the indexed values.

The [byte-slice example](https://github.com/clicklang/click/blob/master/examples/rust-slices/bytes.click)
uses variable-length contracts with existing memory ranges:

<!-- verified-example: mdtests/uint64_index_variable_length.md -->
```click
uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }
```

The length bound reflects the current signed-word memory-range model; it does
not truncate Rust slice metadata. `.len()` alone needs no byte resource and
preserves larger 64-bit lengths. Slice returns, subslices,
indexed compound assignment, other slice element types, and slices in owned-value
MIR functions remain unsupported. Normal numeric contract casts now include
`(int32)`, `(uint32)`, and `(uint64)`.

## Fixed arrays, copies, and checked indexing

Shared `&[T; N]` and mutable `&mut [T; N]` parameters support `u8`, `u32`,
and `i32` elements with concrete, compiler-evaluated lengths. A fixed-array
reference lowers to a typed pointer without a separate length parameter:
`&[u32; 3]` becomes `const uint32*`. The length remains in the prepared
execution and every indexed read, write, or element borrow checks
`index < N` at the full 64-bit `usize` width before forming an address.
Typed pointer arithmetic preserves element widths; word indices do not become
byte offsets. Array storage must fit the current signed-word memory model
(`N * sizeof(T) <= INT32_MAX`).

Builtin `.len()`, local reference aliases and reborrows, and direct fixed-array
reference calls are supported. `.len()` requires no memory authority, including
for zero-length arrays. Reading any element of a zero-length array cannot pass
the checked panic obligation. Reads require `views` or `owns`, and writes
require `owns`; Rust reference types do not supply these resources implicitly.
The compiler checks conflicting borrows, while Click rejects false functional
claims and contracts that fail to establish bounds or memory authority.

The synthetic [fixed-array example](https://github.com/clicklang/click/blob/master/examples/rust-arrays/arrays.click)
covers all three element types, a checked element reborrow, a direct helper
call, parent reuse, and preservation of an untouched word. Its helper owns
only the indexed word, allowing the caller to retain the remaining storage.

```sh
scripts/build-rust-exporter.sh
cargo run --bin click -- import lock examples/rust-arrays/arrays.click
cargo run --bin click -- verify examples/rust-arrays/arrays.click
cargo run --bin click -- audit examples/rust-arrays/arrays.click
```

Initialized local arrays support literals (`[3u32, 5]`), repeats (`[value; 4]`),
and whole-array copies (`let copied = original`, `words = replacement`,
`*target = *source`). Each local has independent automatic storage. Constructor
operands are evaluated in source order before writing the destination; a repeat
operand is evaluated once, even when its length is zero. Copies capture all
source elements before writing and require read authority over the entire
source and write authority over the entire destination. Local arrays can be
borrowed, indexed, and passed to fixed-array reference parameters.

The synthetic [array-values example](https://github.com/clicklang/click/blob/master/examples/rust-array-values/arrays.click)
checks independent copies, replacing an array from its own elements, copies
through references, empty arrays, and constructor calls with observable effects.

Fixed byte arrays coerce to `&[u8]` and `&mut [u8]` in local initialization,
slice reassignment, and direct calls. The slice points at the original array
and carries its fixed length as 64-bit metadata; coercion allocates no storage
and grants no memory authority. Mutable sources can also coerce to shared
slices. Zero-length arrays support length-only calls without memory authority.
The compiler checks borrow validity, and Click still checks slice bounds and
the callee's `views`/`owns` requirements. See the synthetic
[array-to-slice example](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click).

By-value array parameters or returns, nested arrays, array fields, and
non-byte slices remain unsupported. Indexed compound assignment and arrays
in owned-value MIR remain outside the supported subset. The builtin length
operation also supports non-byte fixed arrays by recovering their fixed
length; this does not enable non-byte slices or general library methods.

Modules, imports, macros, semantic attributes, dependencies, unsafe code,
general traits, type/const generics, heap allocation, aggregate parameters and returns, reference
returns, and other integer widths are outside this slice. Unsupported syntax
fails during extraction or direct lowering. This is not general Cargo-project
support.

## While loops and invariants

Unlabeled `while` loops, including nested loops, use the shared checked loop
rules. Sidecars can declare `invariant`, memory/resource clauses, and numeric
`decreases` measures. Entry and preservation are separate obligations;
arithmetic and indexing in the body retain Rust's panic-freedom checks.
A decreasing measure proves termination through the existing loop checker.
Unshadowed HIR locals use their Rust names in sidecars. Shadowed locals and
names starting with `__rust_` retain distinct compiler-generated identities.
Owned-value MIR loops remain outside this increment.

Conditions currently support scalar comparisons, boolean combinations,
negation, casts, and builtin `.len()`. Calls, indexing, and arithmetic in a
condition require repeated preparation of checked operands and are rejected.
`for`, `loop`, labels, `break`, and `continue` remain unsupported.

[`examples/rust-loops/loops.rs`](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.rs)
and its [sidecar](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.click)
verify a scalar counter, checked accumulation, and a byte-slice walk with a
full-width `usize` counter. The walk uses `invariant i <= bytes_len` and
`decreases bytes_len - i`; slice access still requires the signed-word length
bound and `views` authority. The accumulator contract fixes the added value
to one. These are synthetic loop regressions, not a checksum-library proof.
Verification, profiling, auditing, and proof expansion use the shared engine.

```sh
cargo run --bin click -- import lock examples/rust-loops/loops.click
cargo run --bin click -- verify examples/rust-loops/loops.click
```

The [byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
proves a functional loop over arbitrary input bytes. For slices of length
`0..=1000`, its unchanged Rust source returns the exact mathematical sum of
the input at function entry. A prefix fold and the bound
`0 <= to_integer(total) <= 255 * to_integer((int32)(uint32)i)` establish the
result and safety of every intermediate addition. Checked full-width bounds
connect the `usize` counter to the fold's signed-word endpoint. It covers
empty input and supports profiling, audit, and expanded-proof reverification.

## Moves and drops

[`examples/rust-move-drop/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-move-drop/guard.rs)
constructs a guard, moves it, changes borrowed storage, and returns through two
paths. Its checked `Drop` contract restores the original storage value. The
caller proves the result was captured before cleanup and that the storage was
restored on both paths.

Local non-Copy structs support whole-value construction and moves, scope and
early-return cleanup, conditional initialization/moves, and explicit
`std::mem::drop`. Structs can have lifetime parameters and a local `Drop`
implementation. The compiler selects drop order and drop flags through its
structured, acyclic drop-elaborated MIR; Click does not reconstruct cleanup
from source scopes. Destructor bodies require verified sidecar contracts.

Private checked live flags require a live source and dead destination for a
move, and consume the source. Reads and drops require a live value. Cleanup
must consume every destructor-bearing local before return. The flags prevent
stale struct bytes from justifying duplicate moves, duplicate drops, or omitted
cleanup. Struct storage uses existing checked stack allocation and typed field
loads/stores. Moving a reference field carries the same borrowed address; it
does not create allocation or deallocation authority.

Borrowing fields of local owned structs is supported. In
[`examples/rust-field-borrow/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-field-borrow/guard.rs),
a child guard borrows its parent's saved field. Its destructor writes 42 to
that field, and the parent's destructor subsequently writes 42 to the caller.
Existing `owns` contracts suffice: the checked call planner consumes the
returned field owner and the retained storage fragments to supply the next
call. Each actual supplier is consumed once; views and gaps cannot supply
ownership. Regressions also cover parent mutation after explicit child drop,
disjoint mutable field borrows, false final-value claims, and compiler rejection
of conflicting parent access and use after move. The example passes verification,
profiling, audit, expansion, and re-verification without new Click syntax.

rustc establishes source borrow legality. These checks do not yet extract a
complete Rust loan protocol or infer ownership contracts from Rust types.

This slice excludes partial moves, nested owned fields, Copy trait support,
by-value aggregate calls/returns, cycles or unstructured shared MIR regions,
heap owners such as `Box`/`Vec`, and panic unwinding. Owned-value MIR currently
supports scalar/reference assignments and comparisons; arithmetic in these
functions fails extraction. The scalar/reference HIR slice retains its checked
arithmetic support.

```sh
cargo run --bin click -- import lock examples/rust-move-drop/guard.click
cargo run --bin click -- verify examples/rust-move-drop/guard.click
cargo run --bin click -- import lock examples/rust-field-borrow/guard.click
cargo run --bin click -- verify examples/rust-field-borrow/guard.click
```

## Borrow and proof boundary

rustc establishes source type and borrow legality. Click checks the functional
contract and memory access obligations of the extracted execution. `&mut T`
parameters use pointer-shaped sidecar parameters with explicit `owns` clauses;
shared references use explicit `views` where access is required. Borrowed
references carry no allocation or deallocation authority.

This frontend does not infer sidecar authority from a Rust reference. Contracts
must provide the resources they use. Reborrows of caller storage retain the
same modeled pointer: writes through the child are observed through its parent.
The compiler establishes when parent reuse is legal; the kernel establishes
that each modeled access is justified by the supplied resources. Explicit
resource suspension/recovery remains roadmap work.

The trusted boundary includes the pinned compiler, exporter, semantic artifact,
and its translator. The lock detects stale or changed inputs; it is not an
attestation against somebody deliberately replacing the artifact and its lock.
Tests distinguish invalid Rust rejected by rustc from false functional claims
rejected by Click, and check the ordinary CLI and proof expansion path.
