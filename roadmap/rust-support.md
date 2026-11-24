# P1: Rust support on the launch hosts and for crates with dependencies

Priority: P1.

Soundness: incomplete. Click refuses Rust projects it should accept: on macOS
arm64 the Rust front end cannot be installed, and a crate that uses a
third-party crate cannot be imported. Both are refusals with a diagnostic; no
false acceptance is known.

## Ruling and scope

Maintainer direction, 2026-11-10: Click's public claim is that it supports C,
C++, and Rust, with no ranking among them. Two gaps make a Rust user disagree
within minutes of trying it, so both are launch work: the Rust front end
installs on one host only, and a crate with third-party dependencies cannot
be imported.

Maintainer direction, 2026-11-24, settles the scope of both:

- **Hosts.** The Rust front end's launch hosts are the C++ front end's:
  `x86_64-unknown-linux-gnu` and `aarch64-apple-darwin` (the matrix in
  `.github/workflows/cpp-frontend.yml`). The other release hosts in the
  `targets` of `[workspace.metadata.dist]` in `Cargo.toml` (Linux musl on
  x86-64 and AArch64, Linux GNU on AArch64, Windows on x86-64 and AArch64,
  and macOS x86-64) are P2 for both front ends; they keep the
  unavailable-platform diagnostic. The C++ side is recorded in
  [cpp-support.md](cpp-support.md#p1-front-end-delivered).
- **Dependencies.** A third-party crate is a library under the
  [library-interface rule](../docs/concepts/library-interfaces.md): Click
  never imports, verifies or re-implements a dependency's code and sees it
  only through interfaces Click defines. Only the user's own crate is
  verified. Each dependency function or type the crate uses needs a Click
  interface, the same mechanism as core and std items such as `Vec::pop`; a
  call without one is refused by name. Cargo resolves dependencies at capture
  time. Build scripts and procedural macros run at capture and are trusted
  like the compiler. Code that derive macros generate lands in the user's
  crate and is verified like any user code; an unsupported construct there is
  refused, which is acceptable for launch.

This supersedes the 2026-10-15 decision that Linux x86-64 GNU is the whole
Rust launch scope. The
[completed Linux front-end delivery](../design/rust-charon-assessment.md#completed-linux-frontend-delivery)
stays as delivered; this item extends it. Broader Rust language coverage is
not part of this item: unsafe code is [unsafe-rust.md](unsafe-rust.md), and
the rest of the subset is in the [Rust reference](../docs/reference/rust.md).

## Today

- **Hosts.** `click add rust` has a bundle for `x86_64-unknown-linux-gnu`
  only (`.github/workflows/rust-frontend.yml` builds one Linux job), and
  `src/languages/rust/runtime.rs` reports every other host as unavailable
  ([version manager commands](../docs/reference/cli/versions.md)). A
  committed Rust lock verifies on any release host without the front end;
  writing or refreshing a lock does not.
- **Dependencies.** A Rust project unit names one file, or one crate by its
  own module files
  ([locked crates](../docs/reference/rust.md#locked-crates-and-qualified-declarations)).
  Click invokes rustc directly. It does not read Cargo manifests, run build
  scripts, resolve third-party dependencies, or enable features implicitly. A
  crate whose code names another crate fails in rustc. The adler2 proof
  (`design/adler32/`) verifies adler2's own source as the user's crate, not
  as a dependency.
- **Release.** No tagged Click release exists yet. A first tagged release
  whose assets carry both front ends, installed clean-room on each launch
  host, is part of launch for this item and for
  [cpp-support.md](cpp-support.md#p1-front-end-delivered).

## Requirements

1. **Launch hosts.** The Rust front end installs with `click add rust` on
   `x86_64-unknown-linux-gnu` and `aarch64-apple-darwin`. Other hosts keep
   the unavailable-platform diagnostic, and the installer, the
   [version manager reference](../docs/reference/cli/versions.md) and the
   [coverage matrix](../docs/reference/coverage.md) name the two hosts. Locks
   stay byte-identical across the two hosts for equal inputs, as the
   [shared front-end design](#shared-front-end-design) requires.
2. **Crates with dependencies.** The remaining work:
   - **Cargo resolution and locking.** A project unit describes a crate by
     its Cargo manifest and lockfile. `click capture` lets Cargo resolve the
     dependencies, and the Click lock pins and hashes every dependency input
     the compiler reads, so offline verification on a fresh clone needs
     neither the network nor a registry.
   - **Interface lookup for dependency items.** A call to, or a value of, a
     dependency item resolves by its crate-qualified path to a Click
     interface, through the same lookup that maps core and std items to
     their `library/rust/` contracts. The interface's contracts are reported
     as assumptions like any other library interface
     ([trust](../docs/concepts/trust.md#library-interfaces)).
   - **Refusal diagnostics.** A dependency function or type without an
     interface is refused with a diagnostic naming the crate and the item,
     only when the selected roots reach it. An unsupported construct in
     derive-generated code is refused naming the derive and the construct.
   - **Trust.** Build scripts and procedural macros that run at capture are
     recorded as a trust assumption beside the compiler's
     ([What Click trusts](../docs/concepts/trust.md)).

## Intended regression

- **Hosts.** The installed-layout regression of the Linux delivery,
  `tests/rust_release_install.rs::rust_release_archive_installs_and_verifies`,
  installs the release archive, relocates `CLICK_HOME`, reproduces the
  committed `examples/basic-rust` lock byte for byte, and verifies it with the
  front end removed. It must run on both launch hosts in
  `.github/workflows/rust-frontend.yml`, as the C++ one does.
  (The adler2 project is captured and verified only by
  `tests/rust_import/frontend.rs::installed_rust_frontend_extracts_and_verifies_without_rustup`,
  against a source-built front end; no adler2 lock is committed or compared.)
- **Dependencies.** A small fixture crate with one third-party dependency
  from a pinned source, and one verified function that calls into it through
  a Click interface. The test locks it, verifies it offline with the
  dependency source and the front end removed, and checks three refusals: a
  changed dependency source, a dependency missing from the lock, and a call
  into a dependency item that has no interface.

## Violated invariant

A user who installs a Click release can verify a Rust project with that
release alone, on a launch host, when the project is an ordinary crate with
dependencies.

## Acceptance criteria

- `click add rust` succeeds on both launch hosts; other hosts get the
  unavailable-platform diagnostic, and the docs name the two hosts.
- The installed-layout regression passes on both launch hosts, and locks for
  equal inputs are byte-identical across them.
- The dependency fixture locks and verifies offline, and its three refusals
  pass.
- The Rust reference describes the Cargo workflow, how a dependency's
  interface is supplied, and the refusals; trust lists build scripts and
  procedural macros. The "Rust extraction is not packaged yet" wording leaves
  [coverage.md](../docs/reference/coverage.md), and the "does not ...
  resolve third-party dependencies" wording leaves the
  [Rust reference](../docs/reference/rust.md).
- A tagged release carries the Rust front end for both launch hosts.

## Shared front-end design

This section is the shared design for the C++ and Rust front ends, moved
here when the C++ front end was delivered
([cpp-support.md](cpp-support.md#p1-front-end-delivered)); the Rust front
end follows it.
[Project units](../docs/reference/cli/capture.md#project-units) describes project configuration and the lock
format for all three languages.

- **Install layout and versioning.** Each Click version pins exactly one
  version of each front end. Front ends install beside that version of
  `click` in the `CLICK_HOME` layout that `click upgrade` and `click version`
  manage, so that switching versions switches front ends.
  The user can list which front ends are installed, with their versions.
- **Location.** A front end is resolved in a single documented order:
  1. an explicit per-front-end override, for development only;
  2. the installed front end matching the running `click`;
  3. otherwise, an error that says how to install it.

  Both runtimes already follow this order (`src/languages/cpp/runtime.rs`,
  `src/languages/rust/runtime.rs`), and `CLICK_CPP_EXPORTER` is documented
  as a development override. What remains: the
  [environment reference](../docs/reference/cli/environment.md#click_charon)
  presents `CLICK_CHARON` as the way capture finds Charon rather than as a
  development override that falls back to the installed bundle (the runtime's
  own error already calls it one), and `runtime::resolve` keeps a legacy
  `exporter` path parameter that its only caller passes as `None`; remove it,
  since config files carry no front-end paths.
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
