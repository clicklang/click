# Project configuration: one root file for units, targets, toolchains and locks

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. Import
configuration is per sidecar, so two sidecars in one project can verify the
same header under different predefines, header sets, targets and plain-`char`
signedness, and nothing states or checks that they agree:

- C direct mode has no `__STDC_VERSION__` or `__GNUC__`, and an undefined
  macro in `#if` is silently false (`src/languages/c/source.rs:933-936`).
- C compiler import runs GCC with Click's modeled headers and requires
  `__STDC_VERSION__ 201112L`.
- C++ runs Clang 19 over the real system headers.
- C user space uses signed plain `char`, while every C++ fixture compiles
  with `-funsigned-char`, which is not part of the checked C++ profile
  (`src/languages/cpp/schema.rs:1136-1145`).

These are trust-model gaps: there is no single place where a project states
what it builds, for which target and with which toolchain.

By user direction (2026-10-15), C, C++ and Rust are all launch languages, and
a project configuration is the foundation the front-end work builds on. This
issue owns the configuration model. [cpp-support.md](cpp-support.md) and
[rust-support.md](rust-support.md) own their front ends' identity and
coverage. [multiple-compilers.md](multiple-compilers.md) owns ABI and layout
validation. Those front ends consume the units defined here.

## Current state

There is no project-level notion of how code is imported. Each sidecar
`foo.click` finds `foo.click.import.json` next to it by name, and that file's
`language` field selects one of three unrelated importers:

| | C | C++ | Rust |
| --- | --- | --- | --- |
| Config schema | 1 | 6 | 3 or 4 (crate) |
| Toolchain field | `compiler` (GCC path; preprocessing only) | `exporter` (Clang 19 exporter) | `exporter` (Charon) |
| Build information | hand-copied `-I`/`-D` per source | the project's `compile_commands.json` | hand-listed crate `files` |
| Scope per config | a list of sources | one source and one function | one crate root set |
| Lock name | `X.click.import.lock.json` | `X.click.import.json.lock` | `X.click.import.json.lock` |
| Target spelling | `x86_64-linux-userspace`, `x86_64-linux-kernel` | `x86_64-unknown-linux-gnu` | `x86_64-unknown-linux-gnu` |

- **No import config:** plain C runs through Click's own bounded preprocessor
  in direct mode.
- **`click.project.json`:** holds only `target` and `runtime`. It is read from
  the sidecar's own directory, and the target can also be set by a sidecar
  `target` directive and by the import config. All three must agree.
- **Project root:** defaults to the sidecar's directory.
- **Scale:** the repository has 109 per-sidecar import configs.
  `integrations/bitcoin-core-money-range` alone has 12 that repeat the same
  exporter, compilation database, standard and profile.
- **Fixture problems:**
  - `design/charon-trial/zlib` hard-codes host GCC 14 include directories,
    while its lock records GCC 13's `cc1`.
  - Upstream adler2 and zlib files are copied into the Click directory.

## Project models

All of these must work with **one configuration format**.

1. **Joint development.** Spec and code under verification live in one
   repository that the Click user controls. Click's examples are like this.
   Click may recommend a layout.
2. **Full sidecar.** The code under verification is an external tree that the
   Click user does not control. It arrives as a git submodule, a sibling
   checkout or copied files, and **the user manages it**. Click must not
   mandate its layout, file names or build system, and must never write into
   it. The rbtree launch demo (an unchanged, pinned upstream `lib/rbtree.c`)
   and the Bitcoin Core integration are this model.
3. **Multiple units, including cross-language.** One project holds several
   units, for example a C implementation and a Rust implementation. Proofs
   may show they do the same thing. The supported route is that both
   implementations prove one shared Click specification whose functional
   postconditions determine the result. The existing Adler-32 work in
   `design/charon-trial/checksum-correspondence.md` composes separately
   checked zlib C and adler2 Rust results this way, wired up by hand today.
   A direct relational (product-program) proof is out of scope here.

## Design direction

Decided with the user (2026-10-15):

- **One root file and one format** for every model.
- **External trees are user-managed.** Click reads them in place, records the
  identity of every file it reads in the lock, refuses a stale lock, and
  never writes inside them.
- **No layout or naming requirement on code under verification.** Any naming
  convention, such as sidecar-sibling files, applies only on the Click side.

Proposed structure, to be confirmed while implementing:

- **The project root** is the nearest ancestor directory containing the root
  file, as Cargo finds `Cargo.toml`.
- **The root file declares units.** Each unit gives:
  - a language: C, C++ or Rust,
  - a source root: the project itself or an external path,
  - a source of build information,
  - a toolchain,
  - a target.
- **Shared settings are stated once per project or unit,** not per sidecar:
  the toolchain, target, C++ standard and profile, and the C option profile.
- **Sidecars only select:** a sidecar names the sources (and, for C++, the
  functions) it verifies, resolved through the units. Per-sidecar import
  configs are retired or reduced to selection.
- **One target spelling scheme** covers all three languages.
- **Locking:** `click import lock` with no argument locks the whole project.
  There is one lock naming scheme, and lock files and artifacts live on the
  Click side. Verification stays offline.
- **Zero-config path stays:** a lone C sidecar with no root file keeps
  working in direct mode with the default target.

## Open questions

Each has a recommended default, used unless the user decides otherwise.

1. **Build information for a unit we do not control.** Default: read the
   unit's own build description. That is `compile_commands.json` for C and C++
   (which replaces hand-copied C `args` and needs one flag policy for both),
   and Cargo metadata for Rust (which replaces hand-listed crate `files`).
   An explicit description in the root file is the fallback. Click does not
   run the external build system.
2. **Committed locks and artifacts.** Default: commit them, so anyone can
   verify without the toolchains, as today.
3. **Languages within a unit.** Default: one language per unit. Proofs may
   share specifications across units. Calls across units, such as Rust calling
   C through FFI, are out of scope initially.
4. **Targets per unit.** Default: one target per unit in the first version.
   The format must leave room for a unit verified under several targets.
5. **File format.** Default: JSON, extending `click.project.json`, since
   there is no TOML parser in the build today.

## Intended regressions

- **Cross-language project:** the Adler-32 correspondence as one project with
  a zlib C unit and an adler2 Rust unit, each read from an external tree in
  its upstream layout. No upstream file is copied into the Click directory or
  edited. The C and Rust results are related through the shared specification.
- **Full sidecar with a foreign layout:** a fixture whose external tree uses
  paths and names Click did not choose, with an out-of-tree build directory.
  It verifies with no file added inside the tree.
- **Stale external input:** changing a byte in an external source refuses the
  stale lock and names the file.
- **Conflicting targets:** a sidecar or unit that disagrees with the project
  target is refused, with a diagnostic naming both.

## Acceptance

- One documented root file format. Root discovery and the unit model are
  documented in `docs/`. A lone C sidecar without a root file still verifies
  in direct mode.
- C, C++ and Rust are all configured through units. There is one target
  spelling scheme and one lock naming scheme, and shared toolchain and target
  settings are stated once.
- `click import lock` locks a whole project, and `click verify` needs no
  toolchain.
- External source roots are never written, need no particular layout or
  names, and a changed input is detected through the lock.
- The four intended regressions are checked, the first two as examples or
  integrations.
- Existing import configs and `click.project.json` files are migrated, or
  refused with a diagnostic that names the replacement.
- `docs/concepts/own-project.md`, `docs/reference/cli/import.md` and the CLI
  reference describe the new model.
