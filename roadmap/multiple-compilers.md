# Support multiple C compilers and target ABIs

Priority: P2.

Soundness: soundness-adjacent. A verified claim holds for Click's built-in
target model, which is checked against the building compiler only in part.
On the source-bundle route nothing is checked: there is no compiler query,
layout manifest or flag fingerprint. On the compiler-import route the ABI
probe (`abi_probe` in `src/languages/c/compiler_import.rs`) checks plain
`char` signedness, `__LP64__`, `__CHAR_BIT__`, the `__SIZEOF_*__` scalar
sizes and byte order, and an option profile classifies every recorded flag
([`click capture`](../docs/reference/cli/capture.md#validation-and-supported-profile));
struct, union and array layout are still Click's own. A mismatch between the
model and the real target turns directly into false acceptance. No
divergence for LP64 x86-64 is known; the one reproduced instance, unsigned
plain `char` under the user-space target, is fixed
(`mdtests/userspace_plain_char_is_signed.md`). A program built under another
ABI or other flags is outside the claim
([trust](../docs/concepts/trust.md)).

Click currently imports C under one built-in LP64 layout model. The C
standard fixes important semantic rules, such as array contiguity, member
ordering, and the defined domain of pointer arithmetic, but it does not fix
the sizes and alignments of all C types, pointer representation, aggregate
padding, enum representation, bitfield allocation, packing extensions, or
calling conventions. Those details depend on the target ABI, compiler, and
compiler flags. Rust `repr(C)` checks are useful for the host target, but are
not a universal substitute for the C compiler that will build the verified
program.

The current implementation must not silently apply its LP64 assumptions to a
program compiled as LLP64, ILP32, a packed layout, or another compiler-specific
dialect. The same C source may therefore need to be verified independently
under more than one layout profile. This issue owns the cross-cutting work for
compiler and ABI selection, including layout, compiler-produced metadata,
target-specific caching, and supported implementation-defined behavior. A
feature-specific issue may still own the semantics of a new C construct, but
its target-dependent layout work belongs here.

## Violated invariant

`CTarget` (`src/languages/c/target.rs`) has one triple,
`x86_64-unknown-linux-gnu`, and two modes that differ in plain `char`
signedness and predefined macros: `userspace` (the default, `CTarget::SUPPORTED`) and `kernel`.
Both use the one LP64 `CAbi`. The target name is in CLI results, import
locks and incremental markers. Layout itself still comes from the
process-global `CAbi::SUPPORTED` on the parsing entry points in
`src/languages/c/syntax.rs` and in `src/languages/interface.rs`.

Every byte offset, object size, alignment, pointer step, scalar conversion,
and calling-interface fact used in a proof must come from the exact C
implementation configuration that will compile the source. Click must not
prove a layout-dependent claim using facts from a different compiler, target,
or set of ABI-affecting flags.

## Intended regression

1. Verify an unchanged C fixture containing a layout-sensitive record under a
   named target profile and record the profile's sizes, alignments, field
   offsets, union layout, and array stride.
2. Run the same fixture under two profiles whose layouts differ (for example,
   an LP64 and LLP64 profile once the relevant types are supported), and show
   that each proof uses its own layout and certificate/cache namespace.
3. Obtain a layout manifest from the selected compiler and flags, reject a
   stale or mismatched manifest, and accept equivalent compiler invocations
   only when their target/layout fingerprints match.
4. Keep target-independent C semantics shared across profiles while making
   unsupported compiler extensions, packing rules, bitfields, and calling
   conventions fail explicitly until their profile rules are modeled.

## Acceptance criteria

- Parsing, lowering, resource bounds, and verification receive an explicit,
  immutable target/ABI profile; no layout-sensitive path relies on a process
  global equivalent to `CAbi::SUPPORTED`.
- Built-in profiles cover the supported baseline and at least one materially
  different target data model. The profile defines primitive sizes and
  alignments, pointer widths, struct and union rules, array strides, enum and
  bitfield rules where supported, packing behavior, and calling-interface
  details.
- A compiler-backed layout manifest can supply exact sizes, alignments, field
  offsets, union details, and array strides for the selected source and build
  configuration. The manifest records a target/compiler/flags/source
  fingerprint and is rejected when that identity does not match.
- Proof certificates, incremental verification markers, and caches include
  the layout fingerprint. Proof facts from different profiles cannot be
  reused or combined.
- The same source can be verified for a declared target matrix, producing
  independently checked results and actionable diagnostics for unsupported or
  mismatched compiler features.
- Existing LP64 behavior remains unchanged, and `scripts/check.sh` passes.

Related: [the `int8` signed-byte type](../docs/reference/language/c.md);
[Supported struct layout and field access](../docs/reference/language/c.md#struct-subset);
[translation units and preprocessing](../docs/reference/language/c.md#supported-expressions-and-statements)
for the delivered single-profile baseline;
[kernel-scale-preprocessing.md](kernel-scale-preprocessing.md) for remaining
compiler/header integration work.
