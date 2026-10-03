# Linux `lib/rbtree.c` input closure

This directory pins the inputs of one real compilation: `lib/rbtree.c` from
Linux v6.8.12, `x86_64_defconfig`, GCC 13.3.0. It is a **negative discovery
fixture**. Click does not import this translation unit yet, and nothing here
is a verification claim. The gate pins where the import stops today so that
progress shows up as a changed expectation.

It is sized for this one translation unit. It is not a strategy for importing
a whole kernel tree.

## Contents

- [`input-closure.tar.gz`](input-closure.tar.gz): the 224 unmodified files the
  compilation reads (`lib/rbtree.c`, 216 headers from the release archive, and
  7 headers that the kernel build generates), plus the kernel's `COPYING` and
  the two license texts those files name. It is 345 KB.
- [`provenance.json`](provenance.json): the release archive URL and SHA-256,
  the tag and commit, the compiler and `cc1` hashes, the preprocessing
  argument vector and environment, the size and SHA-256 of the preprocessed
  output, and the size and SHA-256 of every closure file.
- [`rbtree.click`](rbtree.click) and
  [`rbtree.click.import.json`](rbtree.click.import.json): the sidecar and the
  compiler-import configuration for the recorded invocation. The sidecar has
  no contracts yet.
- [`make-closure.py`](make-closure.py): rebuilds the archive from a configured
  tree.

`design/kernel-import-stage0.json` is the original capture record. Its
dependency list has 222 files: it came from Kbuild's dependency file, from
which Kbuild removes `include/generated/autoconf.h`, and it does not list
`lib/rbtree.c` itself. The compiler's own dependency output names all 224.

## What the gate checks

`scripts/check.sh` runs two library tests in
`src/languages/c/linux_rbtree_tests.rs`. Neither uses the network or a kernel
build.

`linux_rbtree_closure_matches_its_provenance` runs everywhere. It checks the
archive hash, every member's size and hash, that no recorded file is missing
and no unrecorded file is present, and that the import configuration carries
the recorded arguments.

`linux_rbtree_pinned_translation_unit_stops_at_its_recorded_frontier` needs
the recorded compiler, identified by the SHA-256 of the driver and of `cc1`.
With it, the test checks four things:

1. `click import lock` refuses the configuration at `-O2`, argument 50. The
   configuration carries every recorded argument except `-E` and the source
   operand, which the importer supplies, and selects the `linux-6.8-x86_64-kbuild` option
   profile. That profile accepts every other recorded option and keeps
   `-O2` refused; the classification and reasons are in
   [`docs/reference/cli/import.md`](../../docs/reference/cli/import.md).
   The options are not removed to make the import fit.
2. The recorded preprocessing, run directly in the extracted closure, yields
   exactly the recorded 637,604 bytes.
3. Click's C frontend rejects that artifact first at
   `././include/linux/compiler_types.h:172`, an anonymous union member in
   the artifact's first declaration.
4. The dependency-closure projection that `rbtree.click.import.json`
   selects keeps 32 file-scope declarations of 2,575, and the kept unit
   parses and lowers as a whole. The test pins the 26 functions it defines.

The recorded compiler is Ubuntu 24.04's `gcc-13` package, which is what the
CI runners have. On a host with a different compiler the second test checks
the closure, prints `linux-rbtree: NOT CHECKED` with the reason, and passes:
a different GCC is not a defect in the tree under test. Set
`CLICK_LINUX_RBTREE_REQUIRE_TOOLCHAIN=1` to make that case fail instead.

The configuration omits `HOME` from the recorded environment, and the
importer does not allowlist it, because preprocessing does not read it: the
compiler driver and `cc1` do not name it, a traced run opens nothing under
it, and the output is byte-identical with it unset or set elsewhere. The
direct preprocessing step uses the recorded environment unchanged.

## Measuring the frontier

The first rejection says little about the rest of the artifact. To list
every file-scope declaration with its first rejection, run:

```sh
CLICK_LINUX_RBTREE_INVENTORY=/tmp/rbtree-inventory.tsv \
  cargo test --lib linux_rbtree_pinned
```

Each line has the original location, `accepted` or the diagnostic, and an
excerpt. A rejected declaration is blanked before the next one is tried, so
a declaration that needs it is rejected as well, and each declaration reports
only its first rejection. The measurement parses a growing prefix once per
declaration, so it is quadratic and is not part of the gate. The current
summary is in `issues/kernel-scale-preprocessing.md`.

## Rebuilding the closure

Download nothing inside the gate. To rebuild the archive, obtain the release
archive named in `provenance.json`, check its SHA-256, extract it, and build
the one object with the recorded compiler in a cleared environment:

```sh
env -i PATH=/usr/bin:/bin HOME=/tmp LC_ALL=C LANG=C make x86_64_defconfig
env -i PATH=/usr/bin:/bin HOME=/tmp LC_ALL=C LANG=C make lib/rbtree.o
python3 integrations/linux-rbtree/make-closure.py --linux-tree <tree>
```

The kernel build needs `flex`, `bison`, and the libelf development headers on
the host. The script checks every file against `provenance.json` before it
writes anything, and the archive is deterministic: sorted members, zero
timestamps and owners, fixed modes. A changed archive needs its new hash in
`provenance.json`.

One discrepancy is unresolved. The reproduced `.config` hashes to
`1d9edddb…bf1a90`, not the `75c6fd00…3797a` that the original capture
recorded. The `.config` is not read by this compilation. Every file that is
read matches its recorded hash where one was recorded, and the object file
and preprocessed output match theirs.

## License

The archive contains unmodified Linux kernel source, licensed under
GPL-2.0 with the Linux syscall note for the UAPI headers. The license texts
are in the archive.
