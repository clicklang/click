# P1: A well-designed C++ front end

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known, and unsupported
C++ constructs are refused. The Clang exporter is a documented trusted front
end, but Click does not establish which exporter it trusted. `click import
lock` runs whatever executable the config's `exporter` path names. It checks
only that the output is artifact schema 60 and that the exporter's
self-reported `frontend_version` contains `19.1.7`
(`src/languages/cpp/schema.rs`). The lock records the SHA-256 of a locally
built binary, but nothing compares that hash with a released exporter. A
reviewer would ask how a user knows that the trusted front end is the one
Click was released with. This issue answers that question.

## Ruling and scope

Maintainer ruling, 2026-10-14, on design-review N5 ("C++ and Rust look like
research demos"): C++ support is P1. The delivered Bitcoin Core slices are
enough as the C++ launch demonstration: `MoneyRange`, the `FeeFrac`
arithmetic, `EvaluateFeeDown/Up`, `CFeeRate::GetFee` and `GetFeePerK`,
`GetSizeOfCompactSize`, and the `std::span` helpers through `SpanPopBack`.
The same holds for [the basic C++ example](../examples/basic-cpp/README.md).
P1 does not require more examples or broader C++ coverage.

The P1 work is the front-end pipeline. Getting from a C++ project to a
verified sidecar should be well designed, not ad hoc. The
[completed Linux Rust front end](../design/rust-charon-assessment.md#completed-linux-frontend-delivery)
uses the [shared front-end design](#shared-front-end-design) below.

## Goal

A user with a C++ project installs Click with `install.sh` or `install.ps1`,
describes the project in its [project configuration](../docs/reference/cli/import.md#project-units),
writes a sidecar, and runs `click import lock` and `click verify`. No Click repository checkout, no
LLVM development install, and no custom build are needed. The same lock then
verifies offline on a fresh clone of the user's project on another machine.

## Today's pipeline

Audit of the current path, from a user's point of view:

1. **The exporter is built from source.** `scripts/build-cpp-exporter.sh`
   needs LLVM 19.1.7 development tools (`llvm-config`, `libclang-cpp`) and
   working libstdc++ headers. It compiles the 4,800-line
   `tools/cpp-exporter/main.cpp` into `target/cpp-exporter/` inside the Click
   checkout. The binary links `libclang-cpp` dynamically with an rpath into
   the host's LLVM `libdir`, so it cannot be moved to another machine. The
   installer (`install.sh`, `install.ps1`, and the cargo-dist configuration
   in `Cargo.toml`) ships only `click`. CI already tars the built exporter
   to share it between test shards (`scripts/check.sh`), but releases do not
   include it.
2. **There is no single way to locate the exporter.** Each import config
   names the exporter by a path relative to the config. Every checked-in
   config points into the repository's build output:
   `../../target/cpp-exporter/click-cpp-exporter` in
   `integrations/bitcoin-core-money-range/MoneyRange.click.import.json`.
   Project units, such as `examples/basic-cpp`, take the exporter from
   `CLICK_CPP_EXPORTER` at lock time only.
   C++ mdtests take a different route: they read `CLICK_CPP_EXPORTER`. If it
   is unset they fall back to `CARGO_MANIFEST_DIR/target/cpp-exporter/...`,
   a path compiled into the binary (`prepare_mdtest_inputs` in
   `src/cli.rs`), so an installed `click` points at the build machine's
   checkout. The tests use the environment variable (`tests/cpp_import.rs`,
   `tests/bitcoin_core_money_range.rs`, `tests/libcxx_span.rs`).
3. **There is no version handshake.** The exporter has no version command.
   The artifact schema number is hard-coded twice: `artifact["schema"] = 60`
   in `main.cpp` and `EXPORT_SCHEMA` in `src/languages/cpp/schema.rs`. The
   Clang version is checked only as a substring of a string the exporter
   reports about itself (see Soundness). The lock's `exporter_sha256` is the
   hash of the local build, so the same inputs locked on two machines give
   two different import identities.
4. **The demonstration is reproducible only inside the repository.** Every
   README starts with `scripts/build-cpp-exporter.sh` and `cargo run --bin
   click` from the repository root. The Bitcoin fee proofs exist as
   `.click.in` templates that only `tests/bitcoin_core_money_range.rs`
   instantiates. The full-checkout `MoneyRange` workflow assumes Homebrew
   Clang 19.1.7, CMake, and the extracted packages.
5. **Setup errors name paths, not causes.** A missing exporter surfaces as
   `resolve C++ exporter `…`: No such file or directory`. A mismatched
   exporter surfaces as a schema or profile error after it has run.
   Diagnostics for unsupported constructs are good: the exporter's `fail`
   reports a source location and the construct.

The [project configuration](../docs/reference/cli/import.md#project-units) has since solved three further
problems: build information no longer comes from templated compilation
databases (`prepare.py`, `.json.in` files), one unit replaces an import config
per function, and C++ locks are portable across machines and checkout paths.

What already works and should be kept:

- refresh is separate from offline verification;
- the inputs are hashed, and re-checked across two export runs;
- the exporter runs in a bounded process with an empty environment;
- unsupported constructs are refused, never approximated;
- the artifact checker is independent of the exporter.

## Design requirements

1. **Ship the exporter.** Each Click release includes a prebuilt,
   self-contained exporter for every host platform that supports C++. It
   bundles or statically links its Clang libraries and Clang's resource
   headers, so no LLVM install is needed. It is installed into the versioned
   install layout under `CLICK_HOME`, either by `install.sh` and
   `install.ps1` or by Click on first C++ use, and its checksum is verified.
   A platform without an exporter gets a diagnostic that says so. Building
   from source stays a contributor path, not a user step.
2. **One way to locate it.** Use the resolution order in
   [Shared front-end design](#shared-front-end-design). User configs contain
   no exporter path. No path compiled into the binary from the build
   machine, such as `CARGO_MANIFEST_DIR`, is used as a fallback.
3. **A versioned interface.** The exporter reports its identity: its own
   version, its Clang version, and the artifact schema it emits. Click checks
   that identity before running the exporter and refuses a mismatch, naming
   the expected version. The artifact schema is defined in one place that
   both sides use. Locks record the front end's release identity, so equal
   inputs give equal identities on every machine. Changing the schema stays
   an explicit refresh, as today.
4. **Clear errors.** One diagnostic, naming the cause and the fix, for each
   of these:
   - no exporter installed for this Click version or platform;
   - a front end with the wrong version.

   Unsupported constructs keep their source location and the name of the
   construct.
5. **Reproducible demonstration.** `examples/basic-cpp` and the hermetic
   `MoneyRange` fixture verify from an installed Click, with commands
   documented in their READMEs that do not use `cargo run`. Turning the
   `.click.in` fee templates into plain sidecars is not required.

The build description, lean per-project configuration, portable locks, and
diagnostics for unsupported flags and stale locks are delivered by the
[project configuration](../docs/reference/cli/import.md#project-units).

Documentation: [Language coverage](../docs/reference/coverage.md),
[`click import`](../docs/reference/cli/import.md) and the
[basic C++ example](../examples/basic-cpp/README.md) describe the installed
workflow. The "needs a repository checkout" wording leaves coverage.md when
this lands.

## Shared front-end design

This section is the shared design for the C++ and
[Rust](../design/rust-charon-assessment.md#completed-linux-frontend-delivery) front ends.
Rust delivery is complete for Linux; its installed workflow uses this design.
[Project units](../docs/reference/cli/import.md#project-units) describes project configuration and the lock
format for all three languages.

- **Install layout and versioning.** Each Click version pins exactly one
  version of each front end. Front ends install beside that version of
  `click` in the `CLICK_HOME` layout that `click install`, `click use` and
  `click default` manage, so that switching versions switches front ends.
  The user can list which front ends are installed, with their versions.
- **Location.** A front end is resolved in a single documented order:
  1. an explicit per-front-end override, for development only, named the
     same way for both front ends;
  2. the installed front end matching the running `click`;
  3. otherwise, an error that says how to install it.

  `CLICK_CPP_EXPORTER` and `CLICK_CHARON` either become that override or are
  retired from user documentation. Config files carry no front-end paths.
- **Identity handshake.** Before running a front end, Click asks it for its
  identity and compares that with the compiled-in pin. Rust's
  `src/languages/rust/charon-profile.json` is the model: it pins the
  extractor revision and version, the compiler commit, the toolchain, the
  flags, and the named semantic versions. C++ gets an equivalent profile.
- **Lock files.** Every language shares the lock envelope
  (`src/languages/envelope.rs`) and input handling
  (`src/languages/inputs.rs`). Each front end
  contributes its release identity and semantic profile to that envelope.
- **Errors.** Both languages share the same diagnostic categories and wording
  for a missing front end and a version mismatch.
- **Regression shape.** Each front end has an installed-layout test that
  runs without the repository's `target/` directory, as described under each
  issue's intended regression.

## Intended regression

An installed-layout test, in the gate or nightly, assembles the release
layout into a temporary `CLICK_HOME`: `click`, plus the C++ front end as the
installer would place it. It then:

1. copies `examples/basic-cpp` to a temporary directory outside the
   repository;
2. runs, with no LLVM on `PATH` and no repository `target/` directory, the
   installed `click import lock` and `click verify` for all three sidecars;
3. checks the refusals: a front end with the wrong version identity is
   refused with the named diagnostic, and a missing front end reports how to
   install it.

The hermetic `MoneyRange` fixture runs the same way.

## Violated invariant

A user who installs a Click release can verify a C++ project with that
release alone. The trusted front end is identified by the release, and a
lock records facts about the project and the pinned front end, not about the
machine that wrote it.

## Acceptance criteria

- Releases ship a checksummed, self-contained exporter for each supported
  host, and the installers (or Click on first use) install it into the
  versioned layout.
- Front ends are located only by the shared resolution order. No checked-in
  user config names an exporter path, and no compiled-in fallback path
  remains.
- The exporter reports its identity, Click checks it before export, and the
  artifact schema has a single definition. Locks record release identities
  and are byte-identical across machines for equal inputs.
- The installed-layout regression and its negative cases pass. The C++
  documentation describes the installed workflow.

When these criteria land, the P1 part of this file is done. Whether the
After launch section then becomes a separate P2 issue is the user's call.

## After launch (not P1)

Everything below is the C++ coverage roadmap toward Bitcoin Core. It is P2
and does not block launch. The detailed delivery history of each slice is in
this file's Git history before the 2026-10-14 ruling. The exact supported
profile is documented in [`click import`](../docs/reference/cli/import.md).

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
`std::as_writable_bytes` uses an explicit catalog contract.

The `SpanPopBack` contract, for descriptor pointer `p` and length `N`, from
`src/span.h:75`, with libstdc++ `span` SHA-256
`f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd`:

```text
requires:
  authority to update the span descriptor
  1 <= N <= 1073741823                        // accepted single-range byte-extent limit
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

The bound is the 32-bit byte extent of shared segment resources
(`UINT32_MAX / 4` four-byte elements). The user accepted it for the first
proof; wider shared byte extents are deferred. The native `size_t` storage
and arithmetic are preserved, not retagged.

### Sequencing

New C++ feature admission waits on [object-model.md](object-model.md), which
recovers the accumulated PR #646 work. The
[archived object-model design](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/design/cpp-object-model.md)
records the accepted laws; it is not an upstream support claim.

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
  - omitted default arguments.

  Record (struct) reference locals are refused today. Admitting one must
  also let a proof name it as a scalar reference local is named: a field
  read through `r` is `r.field`, or the local is refused by name with the
  spelling to use ([place-based resource clauses](../design/place-based-resource-clauses.md#reference-locals),
  step 6). Regression: a C++ mdtest with a struct reference local whose
  proof reads a field through it as `r.field`. Broader cleanup and unwinding belong to
  [control-flow.md](control-flow.md).
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
  [cpp-exceptions.md](cpp-exceptions.md). `ser_readdata32` is a later
  candidate. It still needs two things:
  - writable byte-span construction;
  - an ordinary modular output-buffer contract whose body establishes that
    initially unwritten bytes become initialized. An `owns` contract alone
    does not guarantee that.

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

- virtual dispatch beyond the delivered method interfaces in
  [coverage.md](../docs/reference/coverage.md); generic object state is in
  [generic-stack.md](generic-stack.md);
- general inheritance and subobject identity;
- RTTI;
- arbitrary standard-library verification;
- full exception semantics;
- cross-target coverage.

Preserve upstream C++ as existing C is preserved. Adaptations belong in the
importer, the execution model, sidecar contracts and proof tools. Tooling
instability blocks milestone work under `AGENTS.md`.
