# P1: A well-designed Rust front end

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known; unsupported Rust
is refused, and the pinned Charon front end is a documented trusted
dependency. The gap concerns how that dependency is identified. Refresh runs
the executable at the config's `exporter` path, plus a file named
`charon-driver` next to it. It checks only their self-reported `charon
version` and the commit that `rustup run <toolchain> rustc -vV` reports
(`src/languages/rust/charon.rs`). Locks hash locally built binaries that
nothing compares with a released build. A second gap is recorded under
After launch below: rustc's borrow checking alone does not establish that
Click rejects forged sidecar authority.

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
- the lock envelope;
- errors.

This file adds only what is specific to Rust.

## Goal

A user with a Rust crate, within the supported subset, installs Click with
`install.sh` or `install.ps1`, writes a sidecar and import configuration, and
runs `click import lock` and `click verify`. No Click repository checkout and
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

## Today's pipeline

Audit of the current path, from a user's point of view:

1. **Charon is built from source.** `scripts/build-charon.sh` clones
   `AeneasVerif/charon` into `target/charon-source` and checks out the
   pinned revision `5d6b812e…`. It builds debug `charon` and `charon-driver`
   binaries into `target/charon/debug` with `cargo +nightly-2026-09-17`, and
   needs that nightly toolchain with `rustc-dev`, `rust-src` and the
   `x86_64-unknown-linux-gnu` target (`--install-toolchain`). The installer
   ships neither the binaries nor the toolchain. CI already packages both
   binaries and the pinned sysroot to share them between shards
   (`scripts/check.sh` and `scripts/charon-runtime.sh pack|restore`), but
   releases do not include them.
2. **Runtime discovery is implicit.** At refresh, Click finds `rustup` by
   scanning `PATH` and runs the pinned toolchain through it
   (`extract_crate` in `charon.rs`). It finds the driver as a file named
   `charon-driver` beside the configured exporter (`refresh_import` in
   `src/languages/rust/import.rs`). Neither requirement is documented to
   users, beyond "run `scripts/build-charon.sh`".
3. **There is no single way to locate Charon.** Configs name the exporter
   by a path into the repository's build output: `../../target/charon/debug/charon`
   in `examples/basic-rust/borrow.click.import.json`, and
   `../../../target/charon/debug/charon` in the schema-4 example in the
   [Rust reference](../docs/reference/rust.md). Tests and design notes use
   `CLICK_CHARON` (`tests/rust_import.rs`, `design/charon-trial/README.md`),
   which the `click` binary never reads.
4. **Pinning is good, but the identity is per machine.**
   `src/languages/rust/charon-profile.json` is compiled in. It pins the
   extractor revision and version, the rustc commit, the toolchain, the
   flags and the named semantic versions, and a unit test ties it to the
   `charon` Cargo dependency's revision. The C++ front end should adopt this
   model. However, the lock and its import identity include hashes of the
   locally built `charon` and `charon-driver`. Refreshing unchanged inputs
   on another machine therefore rewrites the lock, even though loading never
   checks those hashes.
5. **Historical "trial" naming reaches users.** Examples:
   - the profile identity `click-charon-trial-v1`;
   - `TrialArtifact`;
   - the refusal "Charon trial requires its pinned extractor revision";
   - the accepted `"backend": "charon-trial"` spelling;
   - the configuration-error text about retired legacy extraction.

   The canonical evidence lives under `design/charon-trial/`.
6. **Config and lock formats differ from C++.** The config is schema 3 or 4
   and the lock is schema 8, with fields named `config`, `source`,
   `exporter`, …. The reading, hashing and atomic-write helpers (`read`,
   `write_atomic`, `local_file` in `rust/import.rs`) duplicate their C++
   counterparts.
7. **Crate closures are hand-listed.** Schema 4 requires every file rustc
   reads to appear in `files`. When the list is wrong, the refusal "Rust
   compiler source closure differs from configured crate files" does not
   say which files are missing or extra.
8. **The target and host are fixed.** Extraction targets only
   `x86_64-unknown-linux-gnu`. Releases build `click` for eight targets,
   including macOS, Windows and aarch64 (`Cargo.toml`), and the Charon
   toolchain must exist for whichever of those hosts are supported.

What already works and should be kept:

- refresh is separate from offline loading, and locks are checked in and
  portable;
- the compiler runs on a private snapshot of the sources;
- the environment is reduced to runtime selectors;
- extraction runs as a bounded process;
- the semantic profile is versioned per named semantics.

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

## Acceptance criteria

- Releases ship, or Click fetches and verifies, a pinned `charon`,
  `charon-driver` and rustc runtime for each supported host, installed into
  the versioned layout.
- Front ends are located only by the shared resolution order. No checked-in
  user config names a repository build path, and `rustup` on `PATH` is not
  required.
- Locks record release identities and are byte-identical across machines,
  using the shared lock envelope and input-handling code.
- No "trial" spellings remain in user-facing names or diagnostics, except
  documented compatibility aliases.
- Crate-closure diagnostics name the differing files.
- The installed-layout regression and its negative cases pass. The
  [Rust reference](../docs/reference/rust.md),
  [Language coverage](../docs/reference/coverage.md) and the basic Rust
  README describe the installed workflow.

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

  Those identities must still travel through C0 lowering and bind actual
  memory permission. Local reference access binding and kernel recovery at
  checked frontiers also remain open. A reproduced false acceptance here
  would be `unsound`, and so P1, under the [issue rules](README.md).
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
