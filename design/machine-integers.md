# One machine-integer design for every width

Status: proposed 2026-10-21; accepted by the maintainer 2026-10-22, with
the decisions below. It supersedes the 2026-10-16 wontfix rulings in
[typed-indices.md](typed-indices.md#rulings) on a width-carrying term type
and a single comparison family. It reopens the goal of the closed
`issues/one-integer-term-type.md` (P1 by user direction, 2026-10-16),
`git show 1e37d2df^:issues/one-integer-term-type.md`. The roadmap entry is
[standard-library.md](../roadmap/standard-library.md#one-machine-integer-design).

The site counts below come from text searches of `src/` at `3aea06b9`,
excluding test files. They size the work; they are not an audit.

## The problem

Click supports ten machine integer types: `int8` to `uint64`, `int128` and
`uint128`. `_Bool`, `size_t`, `usize` and `isize` are aliases of these.
Nothing in the kernel says once what a value of one of these types is, how
it converts, or which rules hold for it. Each rule carries its own list of
supported widths, and the lists disagree.

**Representation.** `Bitvector32Term` (`src/kernel/primitives.rs`) has 60
variants and no width field. The width is implied by the operator family,
the constant's shape, a load's kind, or the enclosing `CValue` tag.

| Family | Variants |
|---|---|
| Constants | `Constant(u32)`, `Int64Constant`, `UInt64Constant`, `MachineIntegerConstant` (128-bit) |
| 32-bit operators | 14, signedness chosen by operator (`Divide`, `UnsignedDivide`, ...) |
| `Int64*` operators | 11, with no logical shift and no unsigned division |
| `UInt64*` operators | 11 |
| Conversions | 6 legacy (`Int64From32`, `UInt32From64`, ...), plus `MachineIntegerCast` and `IntegerToMachine` |
| 128-bit operators | none: a 128-bit value is only a constant, variable, load or cast |

`ConditionTerm` has a 32-bit family (4 signed orders, equality, 5 signed
overflow tests) and a 64-bit family (4 signed orders, 4 unsigned orders,
equality, 5 signed overflow tests). It has no 32-bit unsigned order: a
`uint32` order is the signed order of operands XORed with `0x8000_0000`,
which `integer_observations_of_native_comparison` decodes again. There is no
unsigned overflow test at any width, and no 128-bit condition.

Five enums describe widths: `MachineIntegerType`, `MachineIntegerWidth`,
`MachineIntegerFormat`, `LoadKind` (signedness erased at 32 and 64 bits),
and `CarrierWidth`. Two more restrict widths for one purpose:
`SignedDefinedWidth` (Int32, Int64) and `IntegerRangeFoldIndex` (Int32,
UInt64, Integer, with every endpoint interned as `Int32`).

**Width dispatch.** `MachineIntegerType::<variant>` appears 292 times in
non-test source. About 157 more spell it through a local alias, mostly in
`src/kernel/assumptions.rs`, `src/kernel/api.rs` and the `proof` rules.
Each site lists the widths its rule supports:

| Rule | Covers | Omits |
|---|---|---|
| native comparison of exact observations (`assumptions.rs`) | 8 to 64 bits; narrow only over an extension word | 128 |
| Integer reading of a native comparison | int32, uint32, int64, uint64 | narrow as a target, 128 |
| wrapped word equality from an Integer equality | int32, uint32 | all others |
| definedness as Integer bounds | int32 and int64 `+ - *` | unsigned, narrow, 128, `/`, `<<` |
| in-range operation identity (`integer_operation_identity.rs`) | `+ -` at 8 to 64 bits | `*`, 128 |
| operation bounds (`integer_arithmetic.rs`) | unsigned `/ >> %` at 32 and 64 | signed, narrow |
| `Carrier` (`surface/proof/wide_arithmetic.rs`) | int64, uint64 | 32 and below |
| `signed_arithmetic_planner.rs`, `simp.rs` observations | int32 | all others |

**Library.** `library/integer.click` and `library/machine_integer.click`
hold 138 theorems, most of them one fact restated per width. Coverage is
uneven: `add_to_integer` exists at four widths, `divide_to_integer` at two,
about 25 `machine_integer` families at `int32` only, and none at a narrow or
128-bit width. `roadmap/standard-library.md` counts 110 of 162 library
theorems as width-specific.

**Two meanings for a narrow value.** An 8- or 16-bit value rides in the
32-bit word. The constant constructor sign- or zero-extends it, and debug
builds check that a narrow constant is in range. A symbolic narrow value is
"kept in range by the path facts its producer adds" (`term_width.rs`), which
nothing checks. The sources then disagree on what `to_integer` of a narrow
value is when its word is not an extension:

- "A narrow observation reads its type's bits of the word"
  (`assumptions.rs`, native comparison form).
- "Narrower terms are their extended values" (`term_operations.rs`), and
  the in-range identity assumes the same (`integer_operation_identity.rs`).

Non-extension words do occur. A specification's narrowing keeps the source's
32-bit word without a cast node (`docs/internals/mathematical-integers.md`,
cast identity). The Rust specification sum `old(bytes[0]) + 1u8` is a `uint8`
observation of an unreduced `Add` word
(`bugs/a-rust-u8-sum-and-its-written-spelling-lower-to-different-terms.md`).
`docs/internals/kernel.md` says both that "every conversion into a narrow
type owes that range as an obligation" and that C narrowing "adds no
obligation".

Each rule's author resolved this locally. The native comparison rule
accepts a narrow word only when `narrow_word_is_extension` proves it is a
load or a conversion. `IntegerTerm::from_machine` redirects an `int32`
observation of a narrow load to the load's own type, so one value has one
observation. Every rule that rebuilds an observation must then know that
normalization: `definedness_of_integer_bound` did not, and broke
`rust-byte-sum` until it was taught. The sprawl grows with each fix.

## The design

### One format, one meaning

A machine integer *format* is a width (8, 16, 32, 64, 128) and a signedness.
`MachineIntegerFormat` becomes the one descriptor. `MachineIntegerType`
becomes a name for a format, and `LoadKind` names a format plus a byte count
(floats get their own kind). `CarrierWidth` and `SignedDefinedWidth` are
derived from the format. `IntegerRangeFoldIndex` takes any format.

The invariant: **a machine term of format F denotes an element of F's
range**, and `to_integer` of it is that element. There is no
low-bits-of-a-word reading, because no term of format F has a value outside
F. Producers enforce this, not readers:

- Operators are modular in their format: `Add(F, a, b)` is
  `(a + b) mod 2^w`, mapped into F's range. Undefinedness is a separate
  obligation (C signed overflow, Rust panics), as today.
- A conversion is an explicit `Cast(S → F, v)`. C integer promotion and the
  usual arithmetic conversions lower to such casts, so a narrow operand
  promoted to `int` is `Cast(uint8 → int32, v)`, not the same word reused.
- A narrow C store narrows by a cast. A Rust narrow sum is computed in its
  format, or written as an explicit cast from its 32-bit computation.
- A debug check refuses a term whose format its operands do not give it,
  extending today's `term_width.rs` checks from constants to every term.

How a backend stores an 8-bit value, for example in a 32-bit solver word,
is the backend's business and never visible to a rule.

### One term family, one condition family

The term type carries the format on every typed node:

- `Constant { format, value }` replaces the four constant shapes.
- `Binary { format, op, left, right }` and `Unary { format, op, operand }`
  replace the 36 per-width operators. Signed and unsigned division,
  remainder and shift are distinguished by the format, not the operator.
- `Cast { from, to, value }` replaces the 6 legacy conversions and
  `MachineIntegerCast`; `IntegerToMachine` stays the checked conversion
  from `Integer`.
- `Load { memory, address, kind }`, `Variable`, `If`, folds, applications
  and matches are unchanged. A variable's format is fixed by its context, as
  the per-context width audit already enforces.
- Floats become their own term type: they are not integers.

Conditions become `Compare { format, relation, left, right }` and
`Overflows { format, op, left, right }`, for signed and unsigned formats at
every width, beside the existing `Integer*` comparisons. The XOR encoding of
`uint32` order goes away.

The existing constructors (`ConditionTerm::signed_less_than`,
`Bitvector32Term::add`, ...) and the uniform views in `term_shape.rs` stay as
the API most code uses. They then build or read the format-carrying nodes,
so most call sites do not change.

### Rules stated once over a format

Each correspondence between machine and Integer facts is one rule
parameterized by the format, in one module (`kernel/machine_integer/`).
Every caller asks that module, so no caller lists widths:

- **Exact comparison.** `to_integer(a) R to_integer(b)` holds exactly when
  `Compare(F, R, a, b)` does. This holds for every format with no extension
  side condition.
- **Range.** `min(F) <= to_integer(v) <= max(F)`.
- **In-range identity.** `to_integer(Binary(F, op, a, b))` equals
  `to_integer(a) op to_integer(b)` when that value lies in F, for `+ - *`,
  and for `/ %` with the usual divisor conditions.
- **Definedness.** `not Overflows(F, op, a, b)` holds exactly when the
  mathematical result lies in F. This holds at every width and signedness.
- **Modular equality.** An Integer equality over `+ - *` of observations of
  one format implies the word equality in that format (reduction modulo
  `2^w`).
- **Conversion.** `to_integer(Cast(S → F, v)) == to_integer(v)` when
  `to_integer(v)` lies in F. That is always true when F contains S, so
  widening needs no premise. A narrowing cast is modular, and its identity
  needs the range premise.

The certificate rules in `kernel/proof/` (`integer_operation_identity`,
`integer_cast_identity`, `operation_bound`) check these statements for the
format their node names. One soundness argument covers all formats.

### Conversions in the languages

One table, keyed by source and destination format, says what each language
conversion is:

| Conversion | Lowering | Obligation |
|---|---|---|
| C promotion, usual arithmetic conversion | `Cast` (always widening or same width) | none |
| C narrowing assignment or cast | `Cast` (modular, signed included) | none |
| C++20 and Rust `as` | `Cast` (modular) | none |
| Specification `to_int8(z)` ... `to_uint64(z)` | `IntegerToMachine` | the range bounds |
| Specification cast between machine types | `Cast` | its in-range premise when it narrows |
| Rust checked arithmetic | `Binary` in the operand format | the panic check, as `not Overflows` |

The C, C++ and Rust front ends lower to these nodes and keep no
width-specific promotion logic of their own.

### Library

A width-indexed library fact is one statement over a format parameter, not
a family of copies. The two ways to do that are:

1. Generic theorems over a type parameter constrained to machine integers
   (`theorem add_to_integer<T: machine>(a: T, b: T)`), if the generic
   machinery supports it.
2. One template expanded per format when the library loads, with each copy
   checked as today.

Under Integer-default arithmetic most of the 110 width lemmas are bridges
nothing needs: the rules above are kernel facts, and `auto` uses them
directly. What survives is decided family by family in
`roadmap/standard-library.md`, then stated once, in one `click::integer`
module: `click::machine_integer` merges into it (maintainer, 2026-10-22).

### Coverage

A kernel test matrix builds the same terms, conditions and rule
applications at every format and checks they decide alike, where the values
fit. A missing format then fails a test instead of an example. The
library's every-width fixture
(`roadmap/standard-library.md`, "Intended regression") checks the same
families at the surface.

## Reconsidering the 2026-10-16 ruling

The ruling in `typed-indices.md` gave four reasons. Measured now:

- **"About 8,000 match sites".** `Bitvector32Term::` variants appear about
  11,600 times in 147 non-test files. About 3,200 of those are leaves
  (`Variable`, constants), which a merge of the typed operators does not
  touch. The per-width operators and conversions account for about 2,700
  mentions. The `ConditionTerm::Bitvector32*` and `Bitvector64*` families
  account for about 1,900. Most of those go through constructors and
  uniform views that can keep their signatures. The work is large but
  mostly mechanical, and it can be done one operator family at a time.
- **"The term order is load-bearing".** Canonical forms order equalities by
  their smaller operand, using the derived order of the enum. A merged node
  changes that order once. That is a verdict-neutral migration risk, which
  the gate, the nightly corpus and the expansion audit exist to catch. It is
  not a reason the design cannot hold.
- **"`term_shape.rs` already gives the uniform view".** Its views have 62
  callers outside the module. The 292 width-specific matches above are the
  rest, and every recent fix added more.
- **"The 64-bit order reasoning is built".** It is, but each width-specific
  rule still needs its own extension, as the table above shows. Three were
  extended on 2026-10-21 alone, for narrow types.

The ruling also closed the issue's narrow-value criterion ("narrow values
are range-checked where the term is built") by checking constants only. The
two meanings above show the symbolic case is still open.

## How to build it

Each stage is its own PR or series of PRs and leaves every verdict
unchanged. Each one runs the gate, the nightly corpus and the expansion
audit, and adds deterministic scaling regressions where a representation
changes (`docs/internals/verification-efficiency.md`).

### Stage 0. One meaning for a narrow value

- Document the invariant above in `docs/internals/kernel.md` and remove the
  contradictory sentences.
- Extend the debug width checker to refuse a narrow-format term whose word
  is not a canonical element of its format. Producers are: arithmetic on a
  narrow type, narrowing conversions, specification narrowing, and Rust
  narrow sums.
- Run the checker over the mdtests and examples, and fix each producer it
  flags with an explicit cast. Keep each fix verdict-neutral, or file the
  change.
- Afterwards `narrow_word_is_extension` holds for every narrow term, and
  its guard can go.

### Stage 1. Rules stated once

- Move the width-dispatched rules into `kernel/machine_integer/` as one
  function per rule over `MachineIntegerFormat`: exact comparison, range,
  in-range identity, definedness, modular equality, and conversion.
- Fill the gaps the table lists, each with a regression: unsigned
  definedness, narrow and 128-bit comparison readings, multiplication
  identities, signed operation bounds.
- Add the per-format test matrix.
- This stage changes no term representation. It removes the width lists
  from callers and makes coverage checkable.

### Stage 2. One condition family

- Add `Compare` and `Overflows` with a format.
- Point the existing constructors and `as_bitvector_comparison` at them.
- Migrate readers family by family, and remove the XOR encoding of
  `uint32` order.
- 128-bit comparisons join here.

### Stage 3. One term family

- Merge one operator family per PR into `Binary`, `Unary`, `Constant` and
  `Cast`, starting with the 64-bit duplicates, then the 32-bit operators,
  then the six legacy conversions.
- Keep the constructor API. Retire `Bitvector32Term`'s name when it no
  longer describes the type.
- Separate floats into their own term type.
- Load equations take their load's format.

### Stage 4. Front ends and library

- Lower C promotions, C narrowing, Rust narrow arithmetic and casts to the
  conversion table, and remove front-end width matrices
  (`coerce_c_value_to_type_as`, the `promote_c_*_path_value` family).
- State the surviving library families once, per
  `roadmap/standard-library.md`.

### Stage 5. A logical `bool`

- Give Click `bool` its own kernel sort, separate from every integer
  format. Bool connectives and `if` work on it directly.
- Make C `_Bool` and C++ `bool` the {0, 1} machine-integer format, read as
  Click `bool` by `!= 0`.
- Map Rust `bool` to Click `bool`, with the 0-or-1 byte rule at memory
  reads.
- Update the language reference's Booleans section, which today defines
  `bool` as the C values `0` and `1`.

## Risks

- **Canonical order.** Merging nodes changes the derived order that
  canonical forms rely on. Each stage compares verdicts and expansion
  output over the corpus before and after, and keeps any intended change in
  its own commit.
- **Concurrent work.** The kernel changes daily. Stage 3 goes one operator
  family per PR, behind unchanged constructors, so each PR stays small.
- **Performance.** A format is `Copy` and small. Interning keys include it.
  No stage adds a scan or a per-step clone. Scaling regressions run at
  several sizes for any changed hot path.
- **Hidden reliance on the 32-bit word.** Code that reads a narrow value's
  word as an `int32` without a cast surfaces in Stage 0's checker. That is
  the point of doing Stage 0 first.

## Decisions

Maintainer direction, 2026-10-21:

- **Generic library theorems.** A width-indexed library fact is a generic
  theorem over a type parameter constrained to machine integers (option 1
  under [Library](#library)), not a template expanded per format. If the
  generic machinery cannot yet state one, extend it rather than generate
  copies.
- **`bool` is logical; C's `_Bool` is an integer.**
  - Click's `bool` becomes its own logical sort. Its values are `true` and
    `false`. It has no arithmetic and no integer reading. Today the
    reference defines it as "the C `bool` values, exactly `0` and `1`" with
    no separate kernel sort; that changes.
  - Rust's `bool` maps to Click `bool`. Its one integer property, that its
    byte holds 0 or 1, is a validity rule on memory, checked where a byte is
    read as a `bool`.
  - C's `_Bool` and C++'s `bool` are a machine-integer format with range
    {0, 1}. Converting a scalar to it gives `0` or `1`, as C11 6.3.1.2 says.
    Arithmetic on it promotes like any narrow type.
  - A C `_Bool` value used as a Click `bool` is read by the test `!= 0`, as
    a C `bool` compared with `true` already is.
- **C signed narrowing wraps.** A conversion to a narrower signed type
  whose value does not fit is implementation-defined in C (C11 6.3.1.3p3).
  Click reads it as modular, as every supported target defines it, and it
  owes no obligation. A strict mode that asks for one can be added later.
