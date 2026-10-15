# P1: A well-designed Rust front end

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known; unsupported Rust
is refused, and the pinned Charon front end remains a documented trusted
dependency. Installed extraction checks explicit Charon, paired-driver and
compiler identities. Rust locks bind the release and semantic profile rather
than machine-specific executable hashes. Host coverage is still limited to
Linux x86-64 GNU. The separate borrow-authority work recorded under After launch
concerns rejection of forged sidecar authority beyond compiler borrow checking.

## Ruling and scope

Maintainer ruling, 2026-10-14, on design-review N5: Rust support stays P1.
The adler2 Adler-32 work is enough as the Rust launch demonstration, together
with its checked correspondence to zlib, the
[basic Rust example](../examples/basic-rust/README.md) and the other
synthetic examples. P1 does not require more checksum milestones or broader
Rust coverage.

The P1 work is the Charon front-end pipeline. It follows the
[shared front-end design](cpp-support.md#shared-front-end-design) in
[cpp-support.md](cpp-support.md), which covers:

- install layout and version pinning;
- locating front ends;
- the identity handshake;
- errors.

The lock envelope, the build description (including how a crate is
described) and project configuration belong to
[project-config.md](project-config.md). This file adds only what is specific
to Rust.

## Goal

A user with a Rust crate, within the supported subset, installs Click with
`install.sh` or `install.ps1`, describes the crate in its [project configuration](project-config.md), writes
a sidecar, and runs `click import lock` and `click verify`. No Click repository checkout and
no Charon build from source are needed. The user also does not hand-install a
pinned nightly toolchain, or Click installs it for them in one documented
step.

## Delivered launch demonstration

These are delivered; details are in the
[Rust reference](../docs/reference/rust.md) and
[the Adler trial](../design/charon-trial/adler2/README.md).

- **Rust Adler-32.** The unchanged, pinned adler2 2.0.1 `Adler32::compute`,
  `adler32_slice`, the constructors, the getter, `write_slice` and
  `from_checksum` prove the common checksum specification. This holds for
  every length from 0 through 2,147,483,647 bytes, from any canonical
  state. The proofs include termination, byte preservation, every native
  access and arithmetic guard, and incremental use at every split. Locked
  real clients compose two calls, and save and restore a checksum.
- **zlib Adler-32.** The unchanged, pinned zlib `adler32` proves the same
  specification for arbitrary canonical A/B, nonnull input and the same
  length range, on all of its original paths. A real incremental C client
  composes every split.
- **Correspondence.** Checked
  [C/Rust correspondence](../design/charon-trial/checksum-correspondence.md)
  derives equal return words from those independent proofs under matched
  bytes and state, and connects the reset behaviors. It composes
  independently checked programs; it does not claim a verified FFI boundary.
- **Experimental subset.** The Rust reference lists the supported subset:
  - checked scalar arithmetic, branches and direct calls;
  - shared and mutable references with local reborrows;
  - supported records and move/drop protocols;
  - compact scalar arrays and byte slices;
  - stored shared iterators;
  - locked crate closures with qualified declarations.

  Ordinary verification loads locked artifacts offline.

Whole-body correctness, false final A/B claims, and larger proof-tool checks
run nightly. Full smart audits of the original computation exceed the
standard ten-minute bound and give no verdict; ordinary verification is the
check that succeeds.

## Front-end delivery progress

The first installed frontend slice packages the pinned Charon, paired driver,
rustc and runtime libraries for `x86_64-unknown-linux-gnu`. A release workflow
builds the bundle and publishes its checksum; `click install VERSION --rust`
checks and installs it beside that Click version. `click versions` lists the
installed frontend. Rust project units resolve a development override followed
by that installed bundle. Explicit manifest paths and runtime version checks
remove rustup and the user's toolchain from installed extraction. A relocated
installed-layout regression covers extraction, verification, repeated locks,
version refusal and offline verification after removing the bundle. The
release archive now has a separate installer-driven regression: release-built
Charon is packaged once, the real installer consumes that archive/checksum,
and the relocated installation locks/verifies the basic example and adler2
outside the checkout. Packaging pull requests and tagged releases run this
check before publication.

Rust diagnostics now list bounded crate-closure differences and preserve
compiler filename diagnostics for omitted snapshot inputs. The canonical
profile identity is `click-rust-v1`; existing locks and the historical backend
spelling remain checked compatibility aliases without artifact rewrites.
Frontend failures distinguish absent, incomplete and mismatched installations
from development overrides, and name the corresponding recovery action.

Rust lock schema 9 now contributes the pinned release/compiler and complete
profile identity instead of machine-specific Charon executable hashes.
Single-file metadata paths are portable, and release installation checks compare
refreshed basic/adler2 locks with committed locks. Schema-8 locks remain readable;
refresh is explicit. The installed C/Rust demonstration now has a documented
preparation command and checks all producer/helper bodies outside the checkout.
Other host bundles remain; no broader host matrix is claimed.

## Current pipeline and remaining delivery scope

- Rust project units use `CLICK_CHARON` as an explicit contributor override,
  then the versioned installed frontend. Committed Rust fixtures use project
  units; legacy per-sidecar configs remain readable for compatibility.
- Installed extraction uses the bundle's explicit manifest and pinned compiler
  runtime. It needs no rustup or ambient user compiler. The driver pairing,
  compiler commit, version and host checks run before extraction.
- Rust lock schema 9 binds source/configuration/artifact digests to the Click
  release and full extraction/semantic profile. Release and debug-built Charon
  reproduce the same locks; schema-8 identities remain readable offline.
- Crate-closure errors name bounded missing/extra entries, and missing module
  diagnostics retain the compiler filename. Frontend errors give the appropriate
  installed-bundle or contributor-override recovery action. Historical product
  spellings remain only as documented compatibility aliases or artifact metadata.
- The release archive is installed through the real installer and relocated.
  Its checks cover committed basic/adler2 locks, the complete C/Rust checksum
  demonstration, and verification after removing the frontend and emptying PATH.
  The preparation script copies sources/locks and assembles unchanged proof
  fragments; the installed CLI checks producer, helper and correspondence bodies.
- Only `x86_64-unknown-linux-gnu` currently has a packaged Rust host/runtime and
  modeled extraction target. Other Click hosts report that Rust extraction is
  unavailable. Additional host bundles remain the delivery decision; this work
  does not choose that matrix or expand language coverage.

The shared unit/lock format and migration of remaining C fixture configuration
belong to [project-config.md](project-config.md). In particular, the demonstration
verifies the existing locked zlib inputs offline; it does not pretend that the
Rust bundle supplies GCC or refresh the legacy C compiler inputs.

## Design requirements

These are in addition to the
[shared front-end design](cpp-support.md#shared-front-end-design):

1. **Ship Charon and its compiler runtime.** Each Click release provides a
   release-built `charon` and `charon-driver` at the pinned revision, plus
   the pinned rustc runtime they load, for every host platform that supports
   Rust. They install into the versioned layout, or Click obtains them on
   first Rust use and verifies their checksums. The user does not run rustup
   for Click's toolchain, and Click does not depend on whatever `rustup` is
   on `PATH`. A platform without them gets a diagnostic that says so.
2. **Explicit driver and runtime location.** The `charon-driver` and the
   runtime are part of the installed front end, not inferred from a
   neighbouring file name. The handshake checks the driver and the compiler
   commit together.
3. **Release identity in locks.** The import identity binds the profile and
   the front end's release identity, not local binary hashes, so equal
   inputs produce identical locks on every machine. Migrating existing
   checked-in locks is a single explicit refresh.
4. **Remove "trial" from the user-facing interface.** The profile identity,
   error messages and accepted backend spellings use the product name. Each
   kept historical spelling stays only as a documented compatibility alias.
5. **Helpful crate closures.** A wrong `files` list produces a diagnostic
   that lists the missing and extra files from rustc's dep-info. Cargo
   integration and third-party crates remain outside P1.
6. **Updating the pin is a migration.** Updating Charon or the toolchain is a
   new Click release that states its effect on sidecars, such as names of
   compiler temporaries, and requires an explicit refresh. Making
   observations stable across upgrades is after-launch work (see below).
7. **Reproducible demonstration.** `examples/basic-rust` and the locked adler2
   and correspondence fixtures verify from an installed Click, with README
   commands that do not use `cargo run`.

## Intended regression

The Rust counterpart of the C++ installed-layout test, as described in
[cpp-support.md](cpp-support.md#intended-regression):

1. Assemble the release layout, including the Rust front end, in a temporary
   `CLICK_HOME`.
2. Copy `examples/basic-rust` outside the repository.
3. With no repository `target/` directory and no rustup toolchain from the
   user, run the installed `click import lock` and `click verify`.
4. Check that the refreshed lock is byte-identical to the checked-in one.
5. Check the refusals: a wrong-version front end and a missing front end
   each give the named diagnostic, and a wrong crate `files` list names the
   difference.

## Violated invariant

A user who installs a Click release can verify a supported Rust crate with
that release alone. The trusted extractor and compiler are identified by the
release, and a lock depends only on the project and the pinned front end.

## Acceptance criteria and current evidence

| Criterion | Status |
| --- | --- |
| Pinned frontend/compiler bundle for each supported Rust host | Delivered for Linux x86-64 GNU; additional host coverage remains open. |
| Shared resolution order, no repository build path in Rust project units, no ambient rustup requirement | Delivered; relocated installed-runtime and release-archive checks. |
| Locks record release identities and reproduce across builds/locations | Delivered; schema 9, release/debug equality and committed-lock comparisons. |
| Historical product spellings only as documented compatibility aliases | Delivered; stable serialized metadata retained without reinterpretation. |
| Crate-closure diagnostics name differing files | Delivered; positive and omitted/extra input checks preserve old outputs. |
| Installed demonstration and negative cases | Delivered; original basic/adler2, full C/Rust producer/helper proofs, version/missing/closure refusals and offline checks. |
| Reference, coverage and basic README describe installed use | Delivered for the supported subset/host; checksum preparation and exact CLI commands are documented. |

The next substantial scope choice is additional host delivery versus wider
supported Rust. The after-launch items below are preserved as existing context,
not prerequisites for the completed checksum claims.

## After launch (not P1)

The checksum demonstration is complete for P1, and none of these items is
needed to finish a claim already made:

- **Wider checksum range.** Lengths beyond the shared signed specification
  range (2,147,483,647 bytes) remain unproved for both implementations; the
  current claims state that range explicitly.
- **Borrow authority.** Connect explicit exclusive-child suspension and
  recovery to production resource transitions. Compiler borrow rejection
  alone does not establish rejection of forged sidecar authority. The
  [production assessment](../design/rust-borrow-authority-assessment.md)
  records what is delivered:
  - the synchronous borrowed-memory call protocol, with kernel negatives;
  - parent reuse after the child's last use;
  - the read-only import-bound checker for same-block scalar reborrows,
    with indexed access certificates and scaling checks.
  - operation identities carried through lowering into completed kernel reads
    and stores, including cached scalar reads; indexed bindings retain the
    actual pointer and reject another locked import identity. Failed writes
    produce no store observation, and source deltas have ambient-scaling checks.
  - the checked kernel lifecycle for exclusive scalar-reference identities:
    parent suspension, nested dependencies and one-time child recovery, with
    exact owned-support checks and indexed scaling regressions. The restricted
    source integration below now issues and consumes these transitions.
  - completed scalar-reborrow assignment receipts and execution-bound endings
    immediately after selected child stores. Bindings require both operations
    on one path, check the source and actual pointer, and refuse ambiguous
    repeated observations. These receipts do not yet carry local-loan leases
    or authorize recovery.
  - a private scalar-memory lease adapter that withholds the selected owner,
    checks custody in ordinary loads/stores, preserves child writes through
    recovery and rejects copied stale children after ownership returns. Kernel
    execution negatives and indexed adapter scaling checks cover this layer;
    restricted Rust source execution now activates it as described below.
    Calls, reference storage, aggregates and loop summarization remain refused
    while a lease is active.

  - source-bound births and explicit borrow-end operations for straight-line
    scalar borrow forests. An indexed alias/tree pass computes frontiers once;
    nested endings at one frontier run innermost first. Endings resolve live
    invocation handles, reject live children and consume each handle once,
    preserving the original owned support and current memory. Copies and moves
    retain the same identity, even after replacement of the original variable.
    Read/store observations remain read-only. Native store, alias, read-ending
    and nested-frontier fixtures cover helper/caller verification, expansion,
    parent reuse and authority/value negatives. Preparation scaling includes
    source length, aliases, nested depth and repeated shared diamonds.
    Structured acyclic branches now retain one exact live ledger through both
    arms and end at a common continuation. Arm accesses and conditions extend
    the frontier. Fully closed arm-local borrows/copies now use checked ledger
    checkpoints: all new references end, original ownership returns, private
    reference slots are cleared and the exact entry ledger is restored. Fresh
    IDs are not rewound. Nested scopes preserve existing live references and
    current writes; escaping or cross-arm references are refused. Source and
    selected-delta scaling cover this path. Native
    conditional and nested-borrow helpers/callers cover expansion and negatives,
    while kernel tests exercise joins with live custody.

  Wider source coverage remains open: escaping/conditionally live arm references,
  writes to outer reference bindings, early returns, loops, aggregates, shared
  borrow graphs and call/havoc transport
  need checked protocols. Only the
  activated source subset executes local leases. A reproduced false acceptance
  here would be `unsound`, and so P1, under the [issue rules](README.md).
- **Stable proof observations.** Provide source-facing slice, array and
  iterator observations, so that contracts need not depend on compiler
  temporary names or storage details. They must preserve qualified
  identities, shadowing, source spans, snapshot meaning, and correspondence
  with expanded proofs.
- **Consistent library models.** Consolidate the supported resolved
  instances. Document their preconditions, effects, panic behavior and trust
  assumptions. Validate their declarations, and bind model versions into
  prepared identities. Lookalike methods must not acquire models by
  spelling.
- **Composition and scale.** Keep one execution path and shared CFG joins,
  compact repeated initialization, and checked cleanup on every supported
  exit. Add combined regressions, and verify that ordinary verification,
  profile, expansion and audit agree.
- **Broader coverage.** These stay outside the supported subset until a
  selected program needs a precise slice of them:
  - unsafe Rust and interior mutability;
  - returned references;
  - general traits and generics;
  - closures, async and threading;
  - heap support;
  - mutable or adapted iterators;
  - Cargo dependencies;
  - broad standard-library verification.

## Semantic boundaries and delivery rules

rustc establishes source typing and borrow legality. Click checks functional
claims and supplied memory authority. References grant no allocation or
deallocation authority. Keep allocation lifetime, access authority and value
validity distinct. Lock all of these:

- the source;
- the compiler and exporter;
- the target and layout;
- semantic flags;
- models;
- relevant dependencies.

Preserve full-width Rust metadata and range endpoints. Proofs that use signed
index observations must state and check their narrower range explicitly.

Keep the original Rust and C sources unchanged. Repair lowering, resource
rules, contracts or proof tooling instead. The shared construction and
return-destination contract is recorded in
[aggregate construction](../design/aggregate-construction.md). Delete this
issue and its list entry when the front-end acceptance criteria and their
documentation land; move any remaining after-launch items to a P2 issue
only at the user's request.

Durable design references:

- [resource correspondence](../design/rust-resource-correspondence.md);
- [Charon assessment](../design/rust-charon-assessment.md);
- [adapter trial](../design/charon-trial/README.md);
- [checksum assessment](../design/rust-checksum-assessment.md);
- [language design](../design/supporting-more-languages.md);
- [stable views](../docs/internals/stable-views.md).
