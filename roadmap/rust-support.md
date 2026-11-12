# P1: Rust support on every release host and for crates with dependencies

Priority: P1.

Soundness: incomplete. Click refuses Rust projects it should accept: on every
host but one the Rust front end cannot be installed, and a crate that uses a
third-party crate cannot be imported. Both are refusals with a diagnostic; no
false acceptance is known.

## Ruling and scope

Maintainer direction, 2026-11-10: Click's public claim is that it supports C,
C++, and Rust, with no ranking among them. Two gaps make a Rust user disagree
within minutes of trying it, so both are launch work:

1. the Rust front end installs on one host only;
2. a crate with third-party dependencies cannot be imported.

This supersedes the 2026-10-15 decision that Linux x86-64 GNU is the whole
Rust launch scope and a second host is optional. The
[completed Linux front-end delivery](../design/rust-charon-assessment.md#completed-linux-frontend-delivery)
stays as delivered; this item extends it. Broader Rust language coverage is
not part of this item: unsafe code is [unsafe-rust.md](unsafe-rust.md), and
the rest of the subset is in the [Rust reference](../docs/reference/rust.md).

## Today

- **Hosts.** `click version add VERSION --rust` has a bundle for
  `x86_64-unknown-linux-gnu` only. Every other host gets the
  unavailable-platform diagnostic
  ([version manager commands](../docs/reference/cli/versions.md)). Click
  itself is released for eight targets (`targets` under
  `[workspace.metadata.dist]` in `Cargo.toml`): Linux GNU and musl, macOS,
  and Windows, each on x86-64 and AArch64. A committed Rust lock verifies on
  any of them without the front end; writing or refreshing a lock does not.
- **Dependencies.** A Rust project unit names one file, or one crate by its
  own module files
  ([locked crates](../docs/reference/rust.md#locked-crates-and-qualified-declarations)). Click invokes rustc directly.
  It does not read Cargo manifests, run build scripts, resolve third-party
  dependencies, or enable features implicitly. A crate whose code names
  another crate fails in rustc.

## Requirements

1. **Every release host.** The Rust front end installs with
   `click version add VERSION --rust` on every host a Click release is built
   for. If a host cannot carry the pinned Charon and rustc runtime, the user
   rules on dropping it, and the installer and the
   [coverage matrix](../docs/reference/coverage.md) name the hosts that
   remain. Locks stay byte-identical across hosts for equal inputs, as the
   [shared front-end design](cpp-support.md#shared-front-end-design)
   requires.
2. **Crates with dependencies.** A project unit can describe a crate that
   depends on third-party crates, and `click import lock` imports it. The
   lock records every dependency input the compiler reads, so offline
   verification on a fresh clone needs neither the network nor a registry.
   The design states:
   - where dependency sources come from, and how they are pinned and hashed;
   - whether Cargo resolves them or the unit lists them, given that build
     scripts and procedural macros run arbitrary code at import;
   - how a call into a dependency is treated: verified from its locked
     source, or covered by a contract the sidecar declares and the lock
     pins as an assumption. A dependency function must not be trusted
     silently.

   A construct in a dependency that Click does not support is refused with
   a diagnostic naming the crate and the construct, only when the selected
   roots reach it.

## Intended regression

- **Hosts.** The installed-layout regression that the Linux delivery uses
  (relocate the release archive, reproduce the committed `basic-rust` and
  adler2 locks, verify with the front end removed) runs on each supported
  host, in the gate or nightly. One negative case per unsupported host, if
  any remain, checks the diagnostic.
- **Dependencies.** A small fixture crate with one third-party dependency
  from a pinned source, and one verified function that calls into it. The
  test locks it, verifies it offline with the dependency source and the
  front end removed, and checks three refusals: a changed dependency
  source, a dependency missing from the lock, and a call into a dependency
  function that has neither a verified body nor a declared contract.

## Violated invariant

A user who installs a Click release can verify a Rust project with that
release alone, on the machine they use, when the project is an ordinary
crate with dependencies.

## Acceptance criteria

- `click version add VERSION --rust` succeeds on every release host, or the
  remaining hosts are named by a user ruling, the installer, and the
  coverage matrix.
- The installed-layout regression passes on each supported host, and locks
  for equal inputs are byte-identical across them.
- A crate with third-party dependencies locks and verifies offline; the
  dependency fixture and its three refusals pass.
- The reference describes the dependency workflow and how dependency
  functions are verified or assumed. The "other Rust extraction hosts are
  not packaged yet" and "no third-party crates" wording leaves
  [coverage.md](../docs/reference/coverage.md) and the
  [Rust reference](../docs/reference/rust.md) when this lands.
