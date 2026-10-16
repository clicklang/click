# One integer term type that carries its width

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. A kernel
integer term does not record its width, so whether a term is read as 8, 16,
32, 64 or 128 bits, signed or unsigned, rests on each reader's discipline. The
same discipline failed before: `docs/internals/kernel.md` (index and offset
arithmetic) records that `e219bbc8` and `a98a05e4` each found a signedness
confusion "admitting a false theorem". `design/typed-indices.md` notes that a
reader putting a 64-bit bound in a signed 32-bit comparison "is accepted
silently today".

P1 by user direction (2026-10-16).

## Current state and violated invariant

Every scalar `CValue` variant (`src/kernel/primitives.rs`), from `Bool` and
`Int8` to `UInt128`, `Float32` and `Float64`, carries the same
`Bitvector32Term`. Despite its name, that one term type (60 variants) holds
every width:

- constants of several shapes: `Constant(u32)`, `Int64Constant`,
  `UInt64Constant`, `MachineIntegerConstant`;
- a 32-bit operator set, and 64-bit duplicates of it (11 `Int64*` and 11
  `UInt64*` operators);
- six ad-hoc conversions (`Int64From32`, `UInt64From32`, `UInt32From64`,
  `Int64FromUInt32`, `UInt64FromInt32`, `UInt64FromInt64`) beside the
  general `MachineIntegerCast`;
- floating-point operators.

Width lives outside the term: in the enclosing `CValue` tag, in the operator's
name, or in the condition variant. `MachineIntegerType::symbolic_value` builds
one untyped `Bitvector32Term::Variable` and wraps it in whichever tag is
asked for. `ConditionTerm` has a 32-bit family (10 comparisons), a 64-bit
family (14) whose operands are still `Bitvector32Term`, and an `Integer*`
family used for 128-bit values. 128-bit arithmetic is guarded at the root
only (`accepts_wide_term`). 8- and 16-bit values sit in a 32-bit term, and
their range is kept by path facts that producers add, not by any check on
the term. Four enums describe widths: `MachineIntegerType`,
`MachineIntegerWidth`, `MachineIntegerFormat` and `LoadKind`.

The cost is spread through the kernel: `Bitvector32` appears about 15,400
times in 320 files and `Bitvector64` about 700 times in 66. Normalizers,
decision procedures and order reasoning are written per width, and the 64-bit
copies are weaker. `design/typed-indices.md` records that ranges, object
extents and the order walk are still 32-bit only.

The invariant: an integer term knows its width and signedness, and a
comparison or operator between terms of different formats cannot be built.
One set of operators, one set of comparisons and one decision procedure
serve every width.

## Intended regression

Add kernel tests that build the same arithmetic and comparisons at each
width, and check they decide alike where the values fit. Add tests showing
that a comparison of a 64-bit term with a 32-bit term, and an 8-bit term
holding an out-of-range value, cannot be constructed. Keep the existing
`uint64`, `int128` and narrow-integer mdtests passing unchanged, and add
scaling regressions for 64-bit order chains of several lengths.

## Acceptance criteria

- One integer term type records width and signedness. `CValue`'s integer
  variants carry it, and the per-width operator, constant and conversion
  variants are merged.
- One condition family serves every width. The `Bitvector64*` and
  `Integer*` comparison duplicates are removed or justified in this file.
- Narrow values are range-checked where the term is built, not only by path
  facts.
- `design/typed-indices.md`'s 32-bit-only restrictions are lifted or restated
  against the new type, and `docs/internals/kernel.md` describes it.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
