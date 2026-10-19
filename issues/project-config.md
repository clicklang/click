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
[the completed Linux Rust frontend](../design/rust-charon-assessment.md#completed-linux-frontend-delivery)
record their front ends' identity and coverage. [multiple-compilers.md](multiple-compilers.md) owns ABI and layout
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
  - `design/adler32/project/zlib` hard-codes host GCC 14 include directories,
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
   `design/adler32/project/checksum-correspondence.md` composes separately
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
- **Click's own build description.** The project configuration describes how
  each unit is built: per-source arguments for C and C++, and the crate
  description for Rust. Click does not read Makefiles, CMake or other build
  systems, which cannot be interpreted in general, and does not run them.
  This replaces hand-copied C `args`, templated C++ compilation databases
  (`prepare.py`, `.json.in` files) and per-sidecar Rust crate lists.
- **Locks and artifacts are committed** with the project, so anyone can
  verify without the toolchains.

Proposed structure, to be confirmed while implementing:

- **The project root** is the nearest ancestor directory containing the root
  file, as Cargo finds `Cargo.toml`.
- **The root file declares units.** Each unit gives:
  - a language: C, C++ or Rust,
  - a source root: the project itself or an external path,
  - its build description,
  - a target,
  - for C compiler imports, the compiler to run at lock time.

  The C++ and Rust front ends are not named in project files. They are
  located by the resolution order in
  [cpp-support.md](cpp-support.md#shared-front-end-design).
- **Shared settings are stated once per project or unit,** not per sidecar:
  the target, C++ standard and profile, and the C option profile.
- **Sidecars only select:** a sidecar names the sources and functions it
  verifies, resolved through the units. Several functions from one
  translation unit need no per-function configuration. Per-sidecar import
  configs are retired or reduced to selection.
- **One target spelling scheme** covers all three languages.
- **Locking:** `click import lock` with no argument locks the whole project.
  There is one lock naming scheme, and lock files and artifacts live on the
  Click side. Verification stays offline.
- **One lock envelope for all languages:** the lock schema, each front end's
  release identity and semantic profile, input hashes, the artifact hash and
  size, and the import identity, with language-specific fields in a language
  section. One shared implementation covers bounded reading, hashing, stable
  re-reads, atomic writes, and output-collision and path-containment checks.
  Done: every language's entry uses the envelope in
  `src/languages/envelope.rs` with one import-identity formula, earlier
  entries are refused with ``run `click import lock` ``, and the input
  handling is shared in `src/languages/inputs.rs`.
- **Portable locks:**
  - project files, including those in external source roots, are identified
    by paths relative to their unit's root;
  - toolchain, sysroot and front-end resource files are identified by content
    and front-end identity, not by absolute path.

  A committed lock verifies offline on a fresh clone at another path.
- **Diagnostics:** an unsupported flag in a build description is named,
  and a stale lock names the changed file.
- **Zero-config path stays:** a lone C sidecar with no root file keeps
  working in direct mode with the default target.

## Further decisions

The user accepted these on 2026-10-15. JSON, the optimization policy and the
C++ items were chosen explicitly; the rest are the recommended defaults.

1. **Flag policy and optimized builds.** Today C accepts only preprocessor
   flags unless a named option profile admits more, while C++ accepts any
   flag the command carries. Click does not check every assumption an
   optimizer makes. One policy covers C and C++:
   - **One optimization level per project.** The project file states it
     exactly, and `-O2` is the default. Every unit is prepared for that
     level, and a unit's own arguments may not name a different one. Long
     term, a project may verify under several levels; the format leaves
     room for that, but the first version supports one.
   - **The optimized binary is covered by checking, not by safety flags.**
     At `-O2` the compiler assumes the program never overflows signed
     arithmetic, never dereferences null, never accesses an object through
     an incompatible type, and keeps its `restrict` and `nonnull` promises.
     Click already proves the first two. It must also check, or refuse,
     type-punned accesses and the optimizer-promise attributes. Then a
     verified claim holds for the `-O2` build without
     `-fno-strict-aliasing`, `-fno-strict-overflow` or
     `-fno-delete-null-pointer-checks`, and projects such as Bitcoin Core
     keep their real flags.
   - Every other flag in a build description is classified as a
     preprocessor input, a checked semantic setting, or refused.
2. **Existing compilation databases.** They are not an input. A project
   writes its build description once. For example, the Bitcoin fixture's
   CMake command line is translated into the description. A converter can be
   added later if needed.
3. **Languages within a unit.** One language per unit. Proofs may
   share specifications across units. Calls across units, such as Rust calling
   C through FFI, are out of scope initially.
4. **Targets per unit.** One target per unit in the first version.
   The format must leave room for a unit verified under several targets.
5. **File format.** JSON, extending `click.project.json`.
6. **C++ functions.** The C++ exporter exports every function a unit source
   lists into one artifact, so one sidecar can verify several functions of
   the same file.
7. **C++ header pinning.** As for C, headers under the project or a unit
   root are rechecked by their path in that root; headers outside them
   (system, sysroot, toolchain) are pinned by the digest the lock records
   and are not re-read when loading, so C++ locks are portable.

## Progress

- **C units (first increment).** `click.project.json` is found as the nearest
  ancestor of a sidecar and declares `"language": "c"` compiler-import units
  with external roots, unit-wide and per-source arguments, and the
  environment. A sidecar selects unit sources with ordinary relative
  `verifying` paths. `click import lock` on a project writes
  `click.project.lock.json` and `.click/<unit>/<source>.i`; external unit
  roots are rechecked relative to the unit root, so a moved checkout still
  loads and a changed input is refused. Per-sidecar configs still work and
  are refused when a unit also lists the same sources.
- **Rust units.** A `"language": "rust"` unit is one crate with a `crate`
  description and its root in `sources`; its `roots` are the union of what the
  project's sidecars verify (the adler2 `helpers` and `restoration` sidecars,
  separately locked today, both verify against one extraction). Charon comes
  from `CLICK_CHARON` at lock time only. Crate files are recorded per file so a
  changed one is named.
- **C++ units.** A `"language": "c++"` unit gives Clang arguments of its own,
  written into a compilation database Click synthesizes, and each source
  lists its `functions`. The exporter (artifact schema 60) exports every
  listed function into one artifact, so one sidecar verifies several
  functions of a file. Preprocessor inputs under the unit or project roots
  are rechecked relative to them and outside inputs are pinned by digest, so
  C++ unit locks load after the checkout moves.
- **Rust migration.** Every committed Rust fixture and example is a project:
  a Rust unit without a `crate` object is a single-file Rust 2024 program, and
  the adler2 helper, restoration, incremental and resumed sidecars share one
  project with an `adler2` crate unit and two client units. No per-sidecar
  Rust import config remains in the repository; the loaders remain for the
  library-level tests until the command line refuses them.
- **C migration.** `examples/label-build-flags` (with the own-project guide),
  the cross-host fixture and the Linux rbtree integration are projects; the
  rbtree unit reads the extracted closure in place as its `inputs` root, and
  each re-locked artifact is byte-identical to its predecessor. The pinned
  zlib fixture is a project too: Click now models the type-only
  `<stdarg.h>` (`va_list`) and `<sys/types.h>` (`ssize_t`, `off_t`) its
  `zconf.h` includes, and its unit drops the hand-copied host `-isystem`
  directories, so its prepared sources hold no C library text.
- **C++ migration.** `examples/basic-cpp` is a project with one C++ unit and
  committed, portable locks: `prepare.py` and the compilation-database
  template are gone, and it rejoins the nightly audit. The Bitcoin Core
  integration is a project whose `bitcoin` unit's arguments are the real
  CMake command (a gate test checks it); the pinned exporter supplies its own
  Clang resource directory, so no unit states a machine path. One lock serves
  all fourteen sidecars. No per-sidecar import config remains in the
  repository.
- **Command-line refusal.** `click verify`, the proof tools and `click import
  lock` refuse a sidecar's own `<sidecar>.import.json` with a diagnostic naming
  the replacement unit. The mdtest C++ fixtures, the example gate and the tests
  that drive the command line build project files.
- **Per-sidecar imports retired.** The library's per-sidecar loaders and their
  config and lock formats are deleted. The tests describe fixtures in the old
  shape and translate them into project units through shared test helpers;
  `make-fixture.py` reads the project lock and checks the unit's arguments
  against the CMake command.
- **One target spelling.** C targets are spelled like C++ and Rust: the
  triple `x86_64-unknown-linux-gnu`, with `"mode": "userspace"` (default) or
  `"kernel"` in `click.project.json` and `mode "kernel";` in a sidecar. A
  unit's compiler variables are its `env`; the old unit `environment` field
  is refused with the new name. The retired single-name targets are refused
  with their replacement, every C lock records the triple and mode, and the
  committed C locks were re-locked with byte-identical artifacts. C++ and Rust
  unit digests do not bind the C target or mode, so their locks are
  unchanged.
- **Optimization level.** `click.project.json` names `optimization`, `-O2`
  (default) or `-O0`, and every C unit is prepared at it; a unit argument
  naming another level, or defining `__OPTIMIZE__`, is refused. The Linux
  profile no longer requires `-fno-strict-overflow` or
  `-fno-delete-null-pointer-checks`, and the optimizer-promise attributes are
  refused at any optimizing level. An optimizing level keeps
  `-fno-strict-aliasing`, as the maintainer decided on 2026-10-17
  (`design/effective-types.md`). The committed C locks
  were re-locked with byte-identical artifacts.
- **C++ flag policy.** A C++ unit is exported at the project's
  `optimization`, with `-fno-strict-aliasing` at an optimizing level; its
  arguments are classified as preprocessor inputs, checked semantic
  settings, or diagnostic and hardening options, and any other is refused by
  name. At an optimizing level the exporter refuses the optimizer-promise
  attributes on the project's functions. `examples/basic-cpp` and the
  Bitcoin integration were re-locked at `-O2`; Bitcoin keeps its own `-O2`
  argument, which repeats the level.
- **Portable locks.** C and C++ locks, and C++ artifacts, name the unit
  root and the project directory by `$unit` and `$project` (and the pinned
  Clang's resource directory by `$clang-resource`) instead of the preparing
  checkout's path, and their identities cover that form, so re-locking from
  another checkout changes nothing. The committed locks were re-locked; the
  cross-host fixture keeps its earlier absolute lock as a relocation
  regression. A gate test refuses a committed lock that names a checkout path.
- **Projects are the import boundary.** A sidecar's Click imports resolve
  within its project root, the nearest directory holding a
  `click.project.json` (or the sidecar's own directory when none does), and
  an import that leaves it is refused; the root is no longer widened to
  cover a sidecar's imports. A directory target selects every sidecar under
  it, grouped by project. Sidecars that shared models across sibling
  directories became one project each: `examples/rbtree` (model, insert,
  erase and augmented), `examples/pcg`, and `design/adler32`, which holds
  the shared specification, the zlib C unit and the adler2 Rust units under
  one lock, the start of the cross-language regression below. The re-locked
  artifacts are byte-identical. A Rust unit now locks without an existing
  artifact directory.
- **Cross-language project.** The Adler-32 project
  (`design/adler32/project`) reads zlib 1.3.1 and adler2 2.0.1 from vendored
  trees beside it (`design/adler32/vendor`), kept byte for byte at their
  upstream paths; no upstream file is inside the Click project. Click's own
  client units (`incremental.c`, `incremental.rs`, `resumed.rs`) are rooted
  at the directory that holds the project and the vendored trees. The Rust
  importer resolves a `..` in a compiler-reported input, as a
  `#[path = "../../vendor/..."]` attribute produces, only through real
  directories inside the unit root. The upstream units' artifacts are
  byte-identical; the clients' differ only in recorded file paths.
- **Remaining:** the foreign-layout regression below; exceptions to the
  import boundary, such as Click files kept apart from the code in a
  monorepo, are left for a separate setting if needed.

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
- **Portable C++ lock:** `examples/basic-cpp` with committed locks, copied to
  another path, verifies offline from the same locks without `prepare.py` or a
  compilation database template.
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
- Build descriptions live in the project configuration. `prepare.py` and the
  `compile_commands.json.in` template are gone from `examples/basic-cpp`, and
  unsupported flags are refused with a diagnostic naming them.
- All three languages use the shared lock envelope and input-handling code.
  Locks are portable and committed. `examples/basic-cpp` checks in its locks
  and rejoins the nightly audit.
- External source roots are never written, need no particular layout or
  names, and a changed input is detected through the lock.
- The five intended regressions are checked, the first two as examples or
  integrations.
- Existing import configs and `click.project.json` files are migrated, or
  refused with a diagnostic that names the replacement.
- `docs/concepts/own-project.md`, `docs/reference/cli/import.md` and the CLI
  reference describe the new model.
