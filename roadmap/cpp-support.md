# P2: C++ coverage toward Bitcoin Core

Priority: P2.

Soundness: incomplete. No false acceptance is known; constructs outside the
documented profile are refused.

## P1 front end: delivered

The P1 part of this item, a released C++ front end with projects of several
translation units, is complete (user ruling, 2026-11-13): `click add cpp`
installs a checksummed exporter for `x86_64-unknown-linux-gnu` and
`aarch64-apple-darwin` (`.github/workflows/cpp-frontend.yml`,
`tests/cpp_release_install.rs`); see
[project units](../docs/reference/cli/capture.md#project-units) and
[`click add`](../docs/reference/cli/versions.md#languages). The shared
front-end design now lives in
[rust-support.md](rust-support.md#shared-front-end-design).

Deferred to P2:

- Exporter bundles for the other release hosts (Linux musl, Linux AArch64,
  Windows, macOS x86-64). By the 2026-11-24 ruling these are P2 for both the
  C++ and the Rust front end, whose launch hosts are the two above.
- Checking that a project including the host's C++ standard headers
  (`#include <cstdint>`) locks with the installed exporter, and naming a
  missing header package when it does not.

No tagged release exists yet; the first one, installed clean-room on both
launch hosts, is launch work tracked once in
[rust-support.md](rust-support.md#today).

## Coverage toward Bitcoin Core

This is the C++ coverage roadmap toward Bitcoin Core. It does not block
launch. The detailed delivery history of each slice is in
this file's Git history before the 2026-10-14 ruling. The exact supported
profile is documented in [`click import`](../docs/reference/cli/capture.md).

### Delivered launch demonstration

All of these use the unchanged Bitcoin Core v31.1 source, commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, under its real Clang project
profile (LP64, C++20, Clang 19.1.7), in
[`integrations/bitcoin-core-money-range/`](../integrations/bitcoin-core-money-range/README.md):

- `MoneyRange`.
- `FeeFrac`: `IsEmpty`, `+=` and `-=` (including self-aliasing), `Mul`,
  and `Div`. `Div` has exact floor and ceiling results on the joint and
  mode-specific result-fit profiles.
- `EvaluateFeeDown/Up`, in all three native fee domains and with unified
  callers.
- `CFeeRate::GetFee` and `GetFeePerK`.
- `GetSizeOfCompactSize`.
- The pinned `std::span<int>` operations: `size`, `data`, `front`, `back`,
  `operator[]`, `first`, `last`, `subspan`, assignment, and the
  pointer/count constructor. They lead up to the complete `SpanPopBack<int>`
  with modular read and write callers.

Library `Assume` assertions and the selected standard-library constructors are
explicit, pinned assumptions, not verified implementations.
`std::as_writable_bytes` uses an explicit library contract
(`library/cpp/as_writable_bytes.interface.click`).

The `SpanPopBack` contract, for descriptor pointer `p` and length `N`, from
`src/span.h:75`, with libstdc++ `span` SHA-256
`f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd`:

```text
requires:
  authority to update the span descriptor
  1 <= N <= 1073741823                        // accepted single-range byte-span limit
  p[0..N] is live, initialized and readable
  descriptor storage is separate from that backing range

ensures:
  span.data == old(p)
  span.size == N - 1
  result refers to old(p)[N - 1] in the same live allocation
  every original backing element is unchanged
  caller authority over the original backing range is preserved
  no backing storage is allocated, freed, or transferred
```

The bound is the 32-bit byte span of shared segment resources
(`UINT32_MAX / 4` four-byte elements). The user accepted it for the first
proof; wider shared byte spans are deferred. The native `size_t` storage
and arithmetic are preserved, not retagged.

### Sequencing

Each new C++ slice must preserve the invariants and satisfy the relevant
entry/call checks in the [native-interface matrix](../design/object-model-current-audit.md#native-interface-evidence-matrix); there is no blanket
feature freeze. The [object-model design](../design/cpp-object-model.md)
records accepted laws and historical implementation notes, not upstream
support claims.

### Remaining coverage

Each item needs a concrete unchanged source and an exact contract before
implementation:

- **Further fee methods and construction.** The remaining `CFeeRate`
  methods involve one or more of:
  - embedded construction or assignment;
  - aggregate returns;
  - comparison-category values;
  - serialization;
  - strings.

  The portable `DivFallback` path is a separate target, not a substitute for
  the pinned `__int128` implementation. Automatic inference of machine
  observer ranges remains separate from explicit proofs.
- **Expression and lifetime profiles.** Each of these needs an explicit
  sequencing, aliasing, lifetime or admission choice:
  - converted call arguments;
  - call-based brace initialization;
  - calls inside arithmetic or composed expressions;
  - broader memory-reading siblings;
  - nontrivial embedded destruction;
  - header destructor bodies;
  - default arguments beyond integral constants and direct, argument-free
    runtime helpers returning integral values.

  Record (struct/class) reference locals now bind existing objects and keep
  mutable/const aliases, permissions, and storage lifetimes distinct. Proofs
  name their fields as `r.field` and their addresses as `&r`; the named
  `cpp_record_reference_locals_*` regressions cover source admission, ordinary
  verification, expansion, cold checking and retained sessions. Reference call
  results compose through direct calls, forwarding and local bindings.
  Proofs use `result.field` for the returned record's fields and `&result`
  for its address. Direct integer field reads through a nonthrowing read-only
  getter and simple integer field assignments through mutable return references
  are supported. Temporary lifetime extension remains separate coverage work.
  Broader cleanup and unwinding belong to [control-flow.md](control-flow.md).
- **Scalar and import coverage.** Select source before widening a profile
  for any of these:
  - further native wide arithmetic (wide addition, subtraction and
    negation are admitted only if selected source needs them);
  - wide mutable references, memory, aggregates or callbacks;
  - other enum or character types;
  - broader header constant forms;
  - mixed-source executable macros;
  - namespaced method selection;
  - overload signature selectors;
  - same-named record layouts.
- **Bounded bytes and serialization.** The selected first cursor is
  Bitcoin's `SpanReader`, which reports malformed input by throwing
  `std::ios_base::failure`; that exception model is
  [cpp-exceptions.md](cpp-exceptions.md). The fixture-reader
  `ser_readdata32<FixtureReader>` composition is proved on unchanged
  Bitcoin source, including its nested writable-span temporaries and record
  template argument. Its [serialization witness](../design/object-model-current-audit.md#bitcoin-read32-serialization-composition)
  proves all four copied bytes, the exact `uint32_t` result and both cursor
  updates through the reader, serializer, endian helper and wrapper.
  The complete source has ordinary, fully expanded cold and retained-session
  checking, plus bounds, permission, byte-value, result and cursor controls.
  The [modular byte-output](../design/object-model-current-audit.md#modular-byte-output-composition)
  and [writable-byte span](../design/object-model-current-audit.md#writable-byte-span-composition)
  witnesses remain the smaller initializer/authority checks. The real cursor's
  unchanged `SpanReader::ignore` now proves its normal advance and exact
  `std::ios_base::failure` path, returning borrowed authority and preserving
  backing bytes on both exits. Its modular caller also expands and replays.
  The unchanged `SpanReader::read` now verifies through the pinned `memcpy` and
  span contracts. Its [sidecar](../integrations/bitcoin-core-money-range/SpanReaderRead.click)
  proves the copied bytes and cursor advance on success, and the exact exception
  and unchanged cursor on short input. The offline integration test checks
  ordinary verification, expansion, and cold and retained-session replay.
  Decoding through this reader is delivered:
  [`SpanReaderRead32.click`](../integrations/bitcoin-core-money-range/SpanReaderRead32.click)
  proves `ser_readdata32<SpanReader>` returns the four bytes' little-endian
  value and advances the cursor, and on short input propagates
  `std::ios_base::failure` with the cursor unchanged. The next steps are
  typed catches ([cpp-exceptions.md](cpp-exceptions.md)) and
  `ReadCompactSize`.
  Plain `owns` still requires initialized input and does not express an
  initializer.

  The four-write uint32 representation rule, the authenticated `std::byte`
  pointers and the one-way `reinterpret_cast` are delivered (see the
  [byte design](../docs/internals/byte-representation.md)). Byte alias
  access stays restricted to the pinned `std::byte` declaration.
  `ReadCompactSize` additionally brings stream failure and canonical
  encoding rules; keep those separate.
- **Owning containers.** Select one `prevector` operation and state its
  claims explicitly:
  - content;
  - ownership and allocation;
  - copy and move;
  - destruction;
  - small-buffer transition;
  - invalidation.

  Prove exactly which operations invalidate old views, and reject later use
  of them.
- **Larger Bitcoin components.** Choose a bounded script, transaction or
  validation component, and state its safety and functional claims
  separately.

| Slice | Candidate and useful claim | Concepts it forces |
| --- | --- | --- |
| Bounded bytes and serialization | One unchanged span/cursor or serialization helper: bounds, consumed/produced length, byte meaning or round trip. | Loops, range authority, representation and endianness, returned references, malformed-input behavior. |
| Owning containers | One bounded `prevector` operation: content preservation and ownership on each accepted outcome. | Allocation, initialization, copy/move, destruction, small-buffer transitions, invalidation. |
| Larger Bitcoin subsystem | A bounded script, transaction or validation component. | Composition of verified helpers, explicit library contracts, domain specifications. |

### Required invariant for new slices

Every accepted C++ operation keeps faithful, checked execution semantics
through import and lowering:

- receiver identity;
- field ownership;
- aliasing;
- integer definedness;
- lifetime;
- every accepted outcome.

Unsupported reachable behavior fails explicitly. Use one proof language and
the shared verification engine; neither a separate C++ verifier nor renaming
the C-prefixed kernel types is a prerequisite. Unselected declarations in a
header must not force verification of a whole class or of the standard
library, but their layouts and other relevant information are still
validated.

A modular library contract declares whether its implementation is verified
or assumed, and pins it. Resolving a template instance is not a proof of the
library that instance calls. Object-copying a view never duplicates pointee
ownership, and returned references stay tied to the backing storage.
Bitcoin's `Assume` annotations stay contract obligations or explicit
assumptions.

Each new slice preserves unchanged upstream source as its regression, with:

- hostile-artifact and false-claim rejection;
- agreement between ordinary verification, expansion and audit;
- deterministic scaling checks when a hot path changes.

### Shared work and deferred coverage

Reuse the common resource and arithmetic machinery where its semantics agree
with C++. Coordinate with these designs:

- division, with
  [mathematical integers](../docs/internals/mathematical-integers.md);
- bytes, with the [byte design](../docs/internals/byte-representation.md);
- lifetimes, with
  [supporting-more-languages.md](../design/supporting-more-languages.md).

C++ references can alias; do not impose Rust's exclusive-borrow rules on
them. Concurrency belongs to
[concurrency-and-atomics.md](concurrency-and-atomics.md). These are deferred
until a selected proof needs a precise slice of them:

- virtual dispatch beyond the delivered method interfaces, generic object
  state included, in [coverage.md](../docs/reference/coverage.md);
- general inheritance and subobject identity;
- RTTI;
- arbitrary standard-library verification;
- full exception semantics;
- cross-target coverage.

Preserve upstream C++ as existing C is preserved. Adaptations belong in the
importer, the execution model, sidecar contracts and proof tools. Tooling
instability blocks milestone work under `AGENTS.md`.
