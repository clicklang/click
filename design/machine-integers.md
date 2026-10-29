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
`uint128`. `size_t`, `usize` and `isize` are aliases of these. (`_Bool`
was one too; since Stage 5 it is the logical `Bool`, not a format.)
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
| `signed_arithmetic_planner.rs`, `solve.rs` observations | int32 | all others |

After Stage 1 (2026-10-24) the rules live in `kernel/machine_integer/`,
and the matrix there checks this coverage:

| Rule | Covers | Omits, and the stage that adds it |
|---|---|---|
| exact comparison, both directions | every format since Stage 2; narrow through a canonical carrier, 128 bits read back but spelled as Integers | a narrow binder (Stage 3) |
| range and constants | every format | none |
| in-range identity | `+ - *` at 8 to 64 bits | 128 (Stage 3) |
| operation bounds | `/ >> %` at 32 and 64 bits, signed and unsigned | narrow, 128 (Stage 3) |
| definedness as Integer bounds | every format's `+ - *` since Stage 2; filed at int32 and int64 | none |
| modular equality | stated at 32 and 64 bits, filed at 32 | narrow moduli (not sound on 32-bit words), 128 (Stage 3) |
| conversion identity | every pair of formats | none |
| `Carrier`, `signed_arithmetic_planner.rs`, `solve.rs` | unchanged | planner heuristics, after Stages 2 and 3 |

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

1. Generic theorems over a type parameter constrained to a signed or an
   unsigned machine-integer bound (`theorem wrapping_add<T: uintn>(a: T,
   b: T)`, `theorem add_to_integer<T: intn>(a: T, b: T)`), stated with the
   built-in constants `min(T)`, `max(T)` and `bits(T)`
   ([Decisions](#decisions), 2026-10-24), if the generic machinery
   supports it.
2. One template expanded per format when the library loads, with each copy
   checked as today.

Under Integer-default arithmetic most of the 110 width lemmas are bridges
nothing needs: the rules above are kernel facts, and `auto` uses them
directly. What survives is decided family by family in
`roadmap/standard-library.md`, then stated once, in one `click::integer`
module: `click::machine_integer` merges into it (maintainer, 2026-10-22).

Progress: library modules now read specification arithmetic as Integer,
like every other file, so one text has one meaning. A library statement
that means a C result observes it exactly
(`to_integer(value + 1) <= to_integer(upper)`), and each library theorem
still matches its kernel axiom. `click::machine_integer` is now merged into
`click::integer`, under qualified names that keep their width prefixes
(`integer::uint32_wrapping_add`); the generic names of option 1 are the next
step.

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

Done 2026-10-23. What changed:

- The invariant is stated in `docs/internals/kernel.md` ("One meaning for
  a narrow value"), and the sentences that let a narrow word be unextended
  are gone from it and from `docs/internals/mathematical-integers.md`.
- Debug builds refuse a narrow value, narrow observation, or narrow
  conversion operand whose word is not built as a canonical carrier
  (`src/kernel/primitives/term_width/narrow.rs`), at the width checker's
  hooks: an evaluated expression, a stored value, an assumed condition.
  The gate's unit and fixture phases run clean under it.
- The one producer it flagged in the gate was the checked (`Standard`)
  narrowing, which Rust's checked narrow arithmetic and Rust-sidecar
  narrow sums lower to: it returned the operand's 32-bit carrier. It now
  returns the `MachineIntegerCast` node and files, beside its range
  obligations, the certified identity `to_integer(conv(w)) ==
  to_integer(w)`, which holds exactly where those obligations do, and for
  an operand of at most 32 bits the word identity `conv(w) == w`, which a
  comparison of words (Rust's `i8` `result == x / y`) needs. Every verdict
  is unchanged. Rust's modular `as` already spelled the extension
  (`((w & mask) ^ sign) - sign`), which the checker accepts. Two kernel
  tests that stored an unextended byte now store its conversion.
- Binders keep their representation: a fresh variable whose range is
  stated where it is introduced (`c_narrow_integer_range_facts`). The
  checker accepts a variable at a narrow format as such a binder.
- `integer_cast_identity` accepts a widening of an 8- or 16-bit value into
  a containing format through the same word or its 32-to-64-bit
  extension, when the word is built as a canonical carrier or is a binder
  whose stated `int32` range the certificate cites, and `auto` plans it by
  matching the word, so every C widening of a narrow value
  verifies with no premise (`mdtests/auto_widens_*`,
  `mdtests/integer_cast_identity_widens_a_narrow_value.md`).
- `narrow_word_is_extension` is gone. A narrow comparison still takes its
  native form only where that form's `int32` reading normalizes back to
  the same narrow observation, since a binder's word does not record its
  format; that is now a spelling rule, not a soundness guard. Dropping it
  outright changed verdicts: a binder's bounds filed natively read back as
  `int32` observations.

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

Done 2026-10-24, for every gap that needs no new node. What changed:

- `src/kernel/machine_integer/` holds the six rules, plus the operation
  bounds, as functions of the format (`docs/internals/kernel.md`,
  "Machine-integer rules"). Its `representation.rs` is the one map between
  a format and today's per-width nodes; the rule implementations that
  listed widths (the native comparison and its converse, the definedness
  readings, the in-range identity, the operation bounds, the wrapped word
  equality, the cast recognizer, the aliased-operand overflow question) are
  moved there and ask it. Surface callers that spelled ranges or signed
  widths as literals (`selected_arithmetic.rs`, `wide_arithmetic.rs`) ask
  the module's range and definedness formats. Every verdict is unchanged
  except where a gap was filled.
- Filled: multiplication identities at every format with a product node
  (`mdtests/integer_operation_identity_of_a_product.md`,
  `mdtests/auto_observes_a_product_by_a_constant.md`), and signed operation
  bounds at `int32` and `int64`
  (`mdtests/auto_bounds_a_signed_quotient_by_its_operand.md`). Their
  soundness arguments are in `docs/internals/kernel.md`.
- Narrow comparison readings already hold for every canonical carrier, a
  narrow load or conversion, through `IntegerTerm::from_machine`'s
  normalization; the matrix now pins them at 8 and 16 bits. A narrow
  binder's comparison keeps its Integer form, because a variable records no
  format; that needs the format on the term (Stage 3).
- The per-format matrix (`src/kernel/machine_integer/matrix_tests.rs`) runs
  every rule at all ten formats and names each remaining gap with the stage
  that removes it.
- Left for Stage 2, because each needs a condition the term type does not
  have: unsigned, narrow and 128-bit definedness (`Overflows`), and 128-bit
  comparison readings (`Compare`). Narrow and 128-bit operation bounds and
  128-bit identities need operator nodes (Stage 3). The modular equality is
  stated at every width but filed at 32 bits only, as before.
- Width dispatch outside the rules remains: front-end promotion matrices
  (Stage 4), value-tag matches, and planner heuristics that name one width
  (`signed_arithmetic_planner.rs`, `solve.rs`, `Carrier`), which follow the
  term and condition families.

### Stage 2. One condition family

- Add `Compare` and `Overflows` with a format.
- Point the existing constructors and `as_bitvector_comparison` at them.
- Migrate readers family by family, and remove the XOR encoding of
  `uint32` order.
- 128-bit comparisons join here.

Done 2026-10-24. What changed:

- `ConditionTerm` has `Compare { format, relation, left, right }` and
  `Overflows { format, op, left, right }` (`CompareRelation`,
  `OverflowOperation`) in place of its 24 per-width variants. The format
  is a `MachineIntegerType`, `Copy` and part of the derived order and hash.
  Equality reads no sign and is filed at the signed format of its width;
  a narrow comparison is filed at `int32`, whose order its canonical words
  compare exactly. So every fact keeps one spelling.
- The per-width constructors (`signed_less_than`, `uint64_less_equal`,
  `int64_signed_add_overflows`, ...) build the new nodes, and
  `ConditionTerm::machine_compare` and `machine_overflows` dispatch to them
  by format. `as_bitvector_comparison` reports the format with the relation
  or operation. Readers were rewritten to the new nodes; traversals that
  listed every variant (substitution, variable and load collection, the
  havoc identity, reflexivity, the width checker) read one arm per node at
  any format, and `machine_integer/representation.rs` maps formats to the
  nodes directly.
- The derived order of conditions changed once, in its own commit, as
  approved: over a sample of 309 mdtests and examples every audit row and
  `click expand` output was unchanged.
- 128-bit comparisons fold on constants and read back as Integer
  comparisons. An Integer comparison of 128-bit observations keeps its
  Integer spelling (`spells_comparison_natively`): the difference graph and
  interval bounds have no 128-bit nodes and decide it as Integers, and
  spelling it natively lost `wide_division_tests`' division guard.
- Every format has an overflow test. Constant operands fold by the exact
  result's range; `integer_bounds_of_definedness` reads a test at any
  format, and `overflow_fact_of_integer_bound` is its converse. Definedness
  facts are still filed only at `int32` and `int64`, where C's overflow is
  undefined (`files_definedness`); an unsigned test is kernel-internal
  (decision of 2026-10-24). No producer builds an unsigned, narrow or
  128-bit test yet: Rust's panic checks still lower to bounds.
- The matrix has no comparison or definedness gap left.

- The `uint32` order is native, `Compare { format: UInt32, .. }` of the
  operands' words, as the `uint64` order is; the sign-flip encoding
  (`order_operand`, and `unsigned_less_than` building the `int32` order of
  `x ^ 2^31`) is gone. Its readers were migrated by giving `uint32` the
  paths `uint64` has: a `UInt32` domain in the difference graph, paired
  with each word's `Int32` node; a `uint32_order_bounds` endpoint index and
  a place in the format-indexed order walk (`WIDE_ORDER_FORMATS`); `uint32`
  rules in the condition checker (`decide_unsigned32_order`); and native
  readers in the planners, closers and printers. Diagnostics name the
  order "uint32 less-than" (as "uint64 less-than"), where they said
  "signed less-than".
- The `signed_int32` certificate step `interval_sign_bit_flip` is replaced
  by a direct unsigned comparison, `interval_compare L, R ult|ule`, which
  reads each operand's signed interval as unsigned once its sign is known.
  The fixtures that spelled the bias in source were rewritten to the
  `uint32` order they meant.

### Stage 3. One term family

- Merge one operator family per PR into `Binary`, `Unary`, `Constant` and
  `Cast`, starting with the 64-bit duplicates, then the 32-bit operators,
  then the six legacy conversions.
- Keep the constructor API. Retire `Bitvector32Term`'s name when it no
  longer describes the type.
- Separate floats into their own term type.
- Load equations take their load's format.

Progress:

- The 64-bit operators are merged (2026-10-24). `Bitvector32Term` has
  `Binary { format, op, left, right }` (`MachineBinaryOp`) and
  `Unary { format, op, operand }` (`MachineUnaryOp`) in place of its 24
  `Int64*` and `UInt64*` operator variants; `ShiftRight` is arithmetic at
  `int64` and logical at `uint64`. The constructors are unchanged, and
  `machine_binary` and `machine_unary` dispatch to them by format.
  `term_shape.rs` reads both nodes as `Machine(format, op)`. Only `int64`
  and `uint64` have these nodes until the 32-bit operators join; the width
  check refuses any other format. Output is unchanged; the derived order
  now sorts every 64-bit binary before every 64-bit complement.
- The 32-bit operators wait for their leaves to carry a signedness
  (option D, 2026-10-25): today an `int32` and a `uint32` value share one
  word with no node between the two readings, and kernel-internal index
  arithmetic, C conversions, modular equality and the difference graph rely
  on it. The sequence is: (1) the sign cast σ, (2) constants with a format,
  (3) loads with a format, (4) the operator merge; step 3 runs before
  step 2. Step 1 is done
  (2026-10-25): every C conversion between `int` and `unsigned int`, the
  usual arithmetic conversions, the modulo boundary and a sign-cleared
  `unsigned` index build σ, the `MachineIntegerCast` node between `int32`
  and `uint32`, and the kernel reads σ(x) as `x`'s word under rules K1–K4
  ([Decisions](#decisions), 2026-10-25;
  `docs/internals/mathematical-integers.md`, "The 32-bit sign cast"). No
  verdict changed. Before the rules, an explicit cast changed 37 tests (28
  fixture verdicts) across order facts, element indices, arithmetic
  certificates and checked narrowing.
- Step 3, loads with a format, comes before step 2 (maintainer direction,
  2026-10-25) and is done (2026-10-25). `LoadKind::Int32` and
  `LoadKind::UInt32` replace `Bits32`: a C, C++ or Rust read takes its kind
  from the lvalue's type (`LoadKind::of_type`, `LoadKind::of_value`), and a
  pointer read is an `Int32` read as before. A typed read of a cell stored
  at the other 32-bit signedness returns σ of the stored word (rule K5,
  [Decisions](#decisions)); a term-level answer to a load term, which is a
  word, is the stored word (`LoadKind::reads_value` compares word kinds).
  One word, one name: a load variable is a variable, which has no format,
  so a `UInt32` read is named and defined by its word's `Int32` read
  (`LoadKind::word_kind`), as a signed byte read is the conversion of the
  byte's unsigned read. Kernel-internal reads stay `Int32`. A trace prints
  either 32-bit kind as `read<Bits32>`, as before. No verdict changed.
- Step 2, constants with a format, is done (2026-10-25). `Bitvector32Term`
  has `UInt32Constant(u32)` beside `Constant(u32)`, which stays the `int32`
  spelling of every kernel-internal constant. A C, C++ or Rust value at
  `uint32` takes it: literals (`c_uint32_literal`, the C++ scalar literal,
  Rust `u32` literals and suffixes), `MachineIntegerType::constant_term`
  and every conversion fold at `uint32`, `kernel::uint32` and
  `value_from_term` at `uint32` (`Bitvector32Term::in_format32`, one match
  on the root). Its word is `Constant` of the same bits (rule K1): the
  32-bit operator, comparison and overflow constructors and the raw
  32-bit operator builders read it as `Constant` (`into_word32`,
  `constant_word32`), the e-graph interns it as `Constant`
  (`MachineAtom::int32`), the difference graph reads its value
  (`difference_graph::constant`), and the kernel's matches on a 32-bit
  constant's bits read either format. So the format survives only
  on a value at rest, as σ does, and a load at the other signedness of a
  stored constant folds through σ to the other format (K5). The hash and
  the derived order include the format. No verdict changed.
- A `uint32` equality is filed at `uint32` (2026-10-25, rule K6,
  [Decisions](#decisions)). C `==` on `unsigned` operands, a specification
  `==` of `uint32` values and `machine_compare(UInt32, Equal)` build
  `Compare { UInt32, Equal }` (`ConditionTerm::uint32_equal`); every other
  equality stays at `int32`. The operands are words, as for any 32-bit
  comparison. `ConditionTerm` and `BitvectorComparisonOp` compare, hash
  and order by an identity that reads a 32-bit equality's format as
  `int32` (`ConditionTerm::fact_format`), one match on the root, so the
  fact indexes, fact and alpha keys and every equality lookup see one fact;
  the patterns that read a 32-bit equality accept either format, and those
  that read a `uint32` order exclude equality. Diagnostics and traces print
  a `uint32` equality in its own type (`old(u[0]) == 4294967295u32`,
  `uint32 =(…, 4294967295)`), where they printed its `int32` reading
  (`== -1`). No verdict changed.
- Step 4, the 32-bit operator merge, is done (2026-10-29). The 13
  per-operator 32-bit variants and `BitwiseNot` are `Binary { op, format,
  .. }` and `Unary { format, op, .. }` at `int32` or `uint32`, as the 64-bit
  operators are. The map is one to one: a 32-bit operator reads words (K1),
  so the sign-free ones (`+ - * << & | ^ ~`) are filed at `int32`, as
  equality is, and only `Divide`, `Remainder` and `ShiftRight` are built at
  `uint32`; the width check refuses a `uint32` sign-free node and any narrow
  or 128-bit one. No term gains or loses an identity, so no K-rule is
  needed. `Binary` sits where the 32-bit variants were and orders by
  operator before format, so the derived order of the 32-bit terms is the
  old one; the 64-bit nodes moved from after the casts to beside them.
  Patterns use `binary_term!`/`unary_term!` and bare nodes
  `binary_node!`/`unary_node!`; the term shape reads every operator as
  `Machine(format, op)` (`BitvectorBinaryOp` and `BitvectorUnaryOp` lost
  their 32-bit names), `machine_binary`/`machine_unary` dispatch every 32-
  and 64-bit format, and the representation map (`operation_word`,
  `word_operation`, `word_division`) reads one node at the format's
  operator format. Arms that read `Binary { .. }` as 64-bit name their
  formats (`binary_wide_term!`, `unary_wide_term!`), and code that compares
  nodes by discriminant or hashes their shape also compares
  `machine_operator()`. Output is unchanged: every `click verify` output
  and `click audit --verbose` verdict over the integer mdtests and the
  examples is the same, and every expansion count. Work units moved on
  eight examples only, deterministically: session preparation by -1.0% to
  +0.01% (`multifile-registry` the most), claim verification by at most
  0.15%; the 64-bit nodes' derived order and every term's derived hash
  changed. The e-graph keeps its own
  interned node kinds (`Int32Add`, `Int32Binary`, `UInt64Binary`), which are
  signatures, not terms. Scaling regression:
  `machine_operator_chains_cost_the_same_per_node_at_every_format`.


- Every format its own nodes (planned 2026-10-29, [Decisions](#decisions)).
  The 32-bit merge kept one word for `int32` and `uint32`; the next steps
  remove that identity and the narrow word, so a term keeps the structure
  its source wrote. The census at `537534028` found five mechanisms:
  constructors that peel σ, narrow widenings and `UInt32Constant` from
  their operands (`into_word32`, `constant_word32`); σ sharing its
  operand's node in the e-graph, the difference graph and observations
  (`word32`, K1 to K3); a `uint32` read named by its `int32` read and C's
  word reuse between narrow formats; the `uint32` equality and the
  sign-free `uint32` operators filed at `int32` (K6, the merge); and narrow
  values as words (K7, K8, Rust's promoted narrow arithmetic). About 456
  non-test patterns name the sign-free `int32` operators and today also see
  every unsigned one. The sequence, each PR output-neutral until step 4:
  1. A signedness audit (`CLICK_FORMAT_AUDIT`, `scripts/format-audit.sh`;
     `kernel/machine_integer/format_audit.rs`): a debug build records each
     use of the identity by kind, site, fixture, claim and tactic. Done
     (2026-10-29); it changes no term, decision, work unit or output. On
     the gate corpus it reaches 1,438 fixtures; 1,339 re-file a `uint32`
     constant, operator or equality at `int32`, which step 4's own nodes
     replace with no relation. 315 (295 mdtests, 20 examples) also
     use the identity where a relation must replace it: a σ peeled into an
     operator, comparison or observation (132; R0 and R-dist), a narrow
     widening peeled (117; R-comp and K7′), a `uint32` read named by its
     `int32` read (97; R-mem), and narrow values as words (8), Rust's
     promoted narrow arithmetic (4) and C's narrow word reuse (2). No
     `signed_int32` certificate in the corpus, `design/` included, passes
     a `uint32` operator through the signed fragment: its 61 blocks name
     unsigned values only as σ atoms (`x as uint32 as int32`) or in
     `interval_compare … ule`, which reads σ explicitly.
  2. The relations: R0, R-dist and R-comp in the e-graph
     (`equality_graph/terms/machine_relations.rs`), with scaling
     regressions. Done (2026-10-29). While K1 and K8 peel σ and narrow
     widenings at 32 bits they act on the 64-bit conversions (the
     reinterpretation, the low word, the extensions) and on conversions
     into 8 and 16 bits; R0 applies from 32 bits up, where it has no node
     to act on yet, because a narrow operand's word need not be canonical
     and a conversion reads only its low bits. The difference graph's σ
     reading links and K7′ have no node to act on until then either, so
     they land with steps 4 and 6. Every `click verify` output and `click
     audit --verbose` verdict over the integer mdtests and the examples is
     unchanged; work units rose by 0.13% in total, at most 7,953 units in
     one session's preparation and 1,762 in one claim.
  3. Pattern classification: each sign-free `int32` pattern either accepts
     both 32-bit formats or stays signed-only.
  4. `uint32` has its own nodes: constructors stop peeling, K6 goes.
  5. Reads by their own kind, with R-mem; typed index coordinates (G1).
  6. Widenings are nodes: K8 and the word helpers go.
  7. Native narrow operators, specification narrow arithmetic native (G2).
  8. Rust native narrow `+ - * & | ^ ! <<` (G4).
  9. The 64-bit relations and the legacy conversions merged into `Cast`.
  10. Generic `T: intn` / `T: uintn` library theorems.

### Stage 4. Front ends and library

- Lower C promotions, C narrowing, Rust narrow arithmetic and casts to the
  conversion table, and remove front-end width matrices
  (`coerce_c_value_to_type_as`, the `promote_c_*_path_value` family).
- State the surviving library families once, per
  `roadmap/standard-library.md`.

Progress:

- One conversion table (2026-10-26). `kernel/machine_integer/conversion.rs`
  holds it: `lower(source, destination, policy)` gives the node a
  conversion builds (`Identity`, `SignCast` σ, `Cast`, `LowWord`,
  `Extend64`, `Reinterpret64`; a narrow `Word` reuse until the next step)
  and, under the `Checked`
  policy of a specification's cast, whether it owes the destination range;
  `convert_term` builds the node and `convert_value` converts an evaluated
  value. C's conversions (`narrow_integer`, the 128-bit boundary), C++20
  integral conversions and Rust `as` (`convert_value`) take their
  terms from it. Every conversion into an 8- or 16-bit format is now the
  `MachineIntegerCast` C builds, in C++ and Rust too, where they built the
  mask `x & m` or the sign extension `((x & m) ^ s) - s`, and C++ and Rust
  file its range facts as C does. Rule K7 ([Decisions](#decisions),
  2026-10-26) relates the cast to the mask. The cross-language fixture's
  two narrowing gaps closed: C `narrow_u8` (`x as uint8 == (x & 255u32)`) and
  Rust `narrow_i8` (`integer_cast_identity` reads the cast). Printed output
  changed only as approved: C++ and Rust print `x as uint8` and `x as int8`
  where they printed the mask arithmetic, and their traces show the narrow
  range facts C's do. Widening of narrow values still reuses the word
  (rule K8, next), and the C matrices (`coerce_c_value_to_type_as`'s
  integer arms, the `promote_c_*_path_value` family) remain until K8.
  A soundness defect surfaced and is fixed with it: the cast evaluator
  read a C++ or Rust modular cast as a specification's checked one, so a
  narrowing that built a cast node filed the checked identity with its
  operand and no range obligation. Before the table only a 128-bit source
  reached it (`static_cast<unsigned char>(v)` of a `uint128` proved
  `to_integer(result) == to_integer(v)` for every `v`); with the cast in
  place of the mask every C++ and Rust narrowing would have
  (`a_modular_narrowing_files_its_range_and_no_identity_with_its_operand`).
- Narrow widening is a cast (2026-10-26). The widening of an 8- or 16-bit
  value into `int32` or `uint32` is the table's `Cast` in every language:
  C's integer promotions and usual arithmetic conversions
  (`promote_c_int32_path_value`, `promote_c_uint32_path_value`), its
  widening assignments, returns and arguments (`coerce_c_value_to_type_as`),
  C++ integral promotions and Rust `as` (`convert_value`), and Rust
  `From` (`IntegerFrom`, through the C coercion). Rule K8
  ([Decisions](#decisions)) reads the node as its operand's word:
  `word32` and `into_word32` peel it as they peel σ, one match on the root,
  so every 32-bit operator, comparison, overflow test, extension, Integer
  observation, the e-graph, the difference graph and element indices see
  the word they saw when the word was reused. `word_cast32_operand` names
  either cast; the checked narrowing of a widened value is built from its
  operand's format (`checked_narrowing_identity`), and
  `integer_cast_identity` reads a widening by its word only through
  `narrow_widening`'s canonical-carrier check, never by the bare word
  comparison σ uses. A widening into 64 bits keeps its legacy extension
  node over the word. Printed output changed only as approved: a promoted
  narrow value at rest (stored, returned, passed) prints `c as int32` or
  `c as uint32`. C's widening between narrow formats (`int8` or `uint8` to
  `int16`, `uint8` to `uint16`) still reuses the word: K8 covers 32-bit
  destinations only, and C++ and Rust build the K7 cast there.
  Diagnostics that recognize a value as exactly one read or one named
  local (the read-kind explanation, the history notes, the renderer's
  local names and source types) read through a narrow widening, not
  through σ, so they say what they said when the word was reused.
- The front-end width matrices are gone (2026-10-26). C's promotions and
  usual arithmetic conversions are one function,
  `promote_c_path_value(value, format)`, in place of the four
  `promote_c_{int32,uint32,int64,uint64}_path_value`; the integer arms of
  `coerce_c_value_to_type_as` are one arm, `convert_c_integer`, which
  routes a conversion that may owe its range (into a signed type other
  than by σ, or into a narrow type) to `narrow_integer` and builds every
  other from the table; `MachineIntegerType::convert_modulo_value` is gone
  and C++ and Rust call `conversion::convert_value`. The operation's
  format is C11 6.3.1.8's rank rule stated once over formats
  (`conversion::usual_arithmetic_format`), which `scalar_width` asks.
  What stays outside the table: `_Bool` (not a machine format; Stage 5
  made it the logical `Bool`),
  C's word reuse between narrow formats (`int8`/`uint8` to `int16`,
  `uint8` to `uint16`; K8 covers 32-bit destinations only), and the
  legacy mask readers of `integer_cast_identity`, since a byte stored into
  a wider cell still builds `b & 0xFF` (`byte_view::integer_cell_with_byte`).
  Remaining for Stage 4: Rust narrow checked arithmetic as `Binary` in the
  operand's format with `not Overflows` panic checks, in place of its
  `int32` computation and width-specific checks, once Stage 3 gives the
  narrow formats operator nodes; and the library families.

### Stage 5. A logical `bool`

- Give Click `bool` its own kernel sort, separate from every integer
  format. Bool connectives and `if` work on it directly.
- Make C `_Bool` and C++ `bool` the {0, 1} machine-integer format, read as
  Click `bool` by `!= 0`.
- Map Rust `bool` to Click `bool`, with the 0-or-1 byte rule at memory
  reads.
- Update the language reference's Booleans section, which today defines
  `bool` as the C values `0` and `1`.

The plan was revised on review: there is one logical sort, `Bool`, for
every language, and no {0, 1} integer format ([Decisions](#decisions),
2026-10-26, Stage 5).

Progress:

- The kernel sort (2026-10-26). Click `Bool` is the kernel's condition
  sort: a `Bool` term is a `ConditionTerm`, whose `Constant` and
  `Variable` are its literals and binders and whose comparisons are `Bool`
  values. Four value forms that are not comparisons join it, after every
  other variant so the derived order of the existing conditions is
  unchanged (`src/kernel/primitives/bool_sort.rs`): `BoolApplication`, a
  `-> Bool` function's application; `BoolIf`; `BoolEqual`, logical
  equality; and `BoolLoad`, a `bool` cell's read. Every traversal reads
  them (substitution, rewriting, variable, memory and read collection,
  keys, the havoc identity, the width check, canonicalization, which keeps
  them as built), and the printers give each its Surface spelling: `f(x)`,
  `if c { a } else { b }`, `a == b`, the place a read reads. The decision
  and the e-graph apply the logic rules L-If, L-Eq and L-Unfold
  ([Decisions](#decisions)): a conditional is opened only when it is
  itself decided (`PureFactContext::decide_bool_value`); a true equality
  merges its operands' classes, which then share their truth, and a false
  one contradicts the merge; applications of one function to equal
  arguments are congruent; an unfolding files `application == body`
  (`ConditionTerm::bool_unfold_equation`). A binder's truth reaches its
  class whichever was filed first (`bool_binder_truth`). Nothing outside
  the kernel's tests builds the new forms yet, so no verdict, output or
  work unit changed: every mdtest and example gives the same `click
  verify` output and the same `click audit --verbose` rows, work units
  included, except the cold-comparison units, which already vary between
  runs of one binary. Kernel tests are in `src/kernel/assumptions/bool_sort_tests.rs`,
  with scaling regressions at 4, 8, 16 and 32 for nested conditionals and
  equality chains.
- Specification `Bool` (2026-10-27). Click writes the type `Bool`; a
  lowercase `bool` in a Click position is an error, and a C, C++ or Rust
  head keeps its language's spelling. A `-> Bool` application, a `Bool`
  binder, a `Bool` conditional and a `Bool` equality lower to the kernel
  sort, carried in a `CValue::Bool` as their cast to `uint8` (rule C1,
  brought forward from the conversions step, with its e-graph link). C and
  C++ `bool` values are still words and reach `Bool` by `w != 0`. Decision
  D2's refusals apply: a `Bool` compared with an integer, ordered, used in
  arithmetic or joined with an integer arm is an error suggesting
  `b as int32` or `true`/`false`. The spec-bool helpers (`spec_bool_value`
  and its `0 == term` spelling, the complement equation and the C zero-test
  rewrites) are gone. Generics at `Bool` need no new form, since the cast
  is an ordinary `CValue`. Fifteen claims were rewritten (`b as int32`, or
  `true`/`false` arms); no C, C++ or Rust source changed.
- Conversions in every language (2026-10-27). C and C++ `_Bool`/`bool`
  values, parameters, returns, locals and call results are `Bool`, carried
  as their C1 cast `BoolCast { to: UInt8, value }`; a parameter, call result
  or enum field is a named `Bool` binder, and a join makes a fresh one.
  Integer to `Bool` is `x != 0` (`nonzero_test`, built as `bool_not` of an
  equality); `Bool` to integer is C1's cast, with C1c (a cast unequal to 0
  is 1). The `BoolRange` entry fact is replaced by C1b's range facts
  (`c_bool_cast_range_facts`), filed at C entry and at C lvalue reads. C++
  casts to `bool` are the test, and Rust `b as u8` is C1. C `a == b` over
  two `bool`s is logical equality.
- Memory (2026-10-27). The byte rule: a store writes C1's byte, and a read
  of a `bool` cell is `byte != 0` over the ordinary byte load
  (`ConditionTerm::BoolLoad` stays unbuilt, since the byte load already
  names the read by its version). A write into a `bool` cell at another
  kind, or a byte view of one, is refused
  (`mdtests/a_bool_cell_is_not_written_through_another_type.md`,
  `mdtests/a_bool_cell_is_not_copied_into_as_bytes.md`).
- Rust values (2026-10-28). Rust comparisons and connectives are `Bool`
  values with no path split (D5: `CIntegerCastMode::BoolValue`,
  `c_bool_value`, `ConditionValueScope`); enum fields, `Option<bool>` and
  `bool` slice elements are covered, and the six cross-language fixture
  cases re-locked the C++ and Rust imports. The extra Rust split in
  `below_i32`/`below_u32` is gone. A signedness conversion's sign test is
  read as its half-range test, `(intN)u < 0` exactly when
  `u > 2^(N-1) - 1`, at 8, 16, 32 and 64 bits
  (`src/kernel/assumptions/condition_reasoning/sign_bit.rs`).
- The records (2026-10-28): the kernel's rules table, the mathematical
  integers note, the C, C++ import and language references, and the
  Decisions entry below.

Open follow-ups:

- **`&bool` and `&[bool]` are unsupported** in Rust, as are C pointers to
  `bool` and `bool` field places. Suggested design: one bool-cell pointer
  type shared by C `bool *`, C++ `bool*` and Rust `&bool`/`&[bool]`, under
  the byte rule. C proves the 0-or-1 requirement on each read through it;
  Rust gets it from its type's validity invariant.
- **The stored-bool spelling gap** (`step_below` in
  `design/charon-trial/integer-widths/widths.click`). A branch fact on a
  stored `bool` has no source spelling, so selected-premise arithmetic
  drops its Integer reading as an `UnspelledReading`. The proof is written
  out as a split, with a comment, until the fact can be spelled.

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
- **`bool` is logical; C's `_Bool` is an integer.** Superseded on
  2026-10-26 (Stage 5): C's `_Bool` and C++'s `bool` denote the logical
  `Bool`, and there is no {0, 1} integer format; see that entry below,
  and the 2026-10-28 entry that records the model as built.
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

Maintainer direction, 2026-10-24:

- **Unsigned definedness is not a surface predicate.** Surface
  `defined(...)` is about undefined behavior only, so for C unsigned `+`,
  `-` and `*` it is always true. The unsigned `Overflows` condition of
  Stage 2 is kernel-internal: Rust panic checks use it, and it relates a
  wrapping result to its exact value. No new surface predicate is added;
  "does not wrap" stays a bound, such as `to_integer(a) + to_integer(b) <=
  MAX`.
- **Pure reordering is approved.** Merging node families (Stages 2 and 3)
  changes the derived order canonical forms use, which may reorder terms
  in `click expand` output and in diagnostics. A pure reordering needs no
  further approval. Any change in wording or content still goes to the
  maintainer.
- **Generic library bounds.** Generic machine-integer library theorems use
  the bounds `T: intn` (`int8` to `int128`) and `T: uintn` (`uint8` to
  `uint128`), with the built-in constants `min(T)`, `max(T)` and `bits(T)`.
  There is no union bound for now: a fact that holds regardless of
  signedness is stated twice, or `T: intn | uintn` is added later if it is
  needed. This is design only; it is not implemented yet.
- **Type-directed specification arithmetic.** Arithmetic on machine values
  takes its meaning from the type its result is used at; where there is no
  expected type, the author writes one. An Integer position (a comparison
  that reads as Integer, an `Integer` parameter, field or result, `let s:
  Integer`, and the arms of a match or branches of an `if` there) makes
  `+`, `-`, `*` and negation exact over `to_integer` observations; a
  machine position keeps the C operation at that type. An untyped `let` whose value does arithmetic on a
  machine value is an error that names both annotations; an untyped `let`
  has its value's type, so arithmetic on an earlier Integer `let` is
  Integer arithmetic. Unsuffixed literals stay Integer, except that a typed
  `let s: int64 = 5;` gives its literal the declared type, range-checked.
  The reason: one rule, read from types, replaces the
  syntactic spine rule, and extracting a subexpression into a `let` can no
  longer silently change its meaning. Status: the branches of an `if` are
  Integer positions since the kernel gained an Integer conditional
  (`IntegerTerm::If`, 2026-10-25); before that an Integer position observed
  the whole conditional. Predicates' `Integer` parameters and `Integer`
  resource parameters are not supported by lowering yet, so they are not
  Integer positions either; an `Integer` resource field's `fold` value is
  one.

Maintainer direction, 2026-10-25:

- **The 32-bit sign cast is read as its word.** σ_{S→F}(x), the
  `MachineIntegerCast` from `int32` to `uint32` or back, denotes
  `to_integer_S(x) mod 2^32` read in `F`. The kernel takes four rules for
  it:
  - K1 (word identity): `σ(x) == x` as a 32-bit word; σ(x) and `x` are one
    e-graph class.
  - K2 (observation): `to_integer` of σ(x) at `int32` or `uint32` is
    `to_integer` of `x` at that format.
  - K3 (orders and indices): the difference graph, the order-fact indexes,
    the certificate readers (`signed_int32`, `arithmetic`, `normalize
    using`, `integer_cast_identity`) and the memory index rules read σ(x) as
    `x`.
  - K4 (modular equality): an observation of σ(x) contributes `x`'s word.

  Soundness: reduction modulo 2^32 and two's-complement reading are inverse
  bijections between each format's range and the 32-bit words, so
  `bits(σ(x)) = bits(x)`, and every 32-bit operator, comparison and
  observation depends only on its operands' bits.
- **K5 (memory), 2026-10-25.** A 32-bit read at signedness F of a cell
  holding a value stored at the other signedness S returns σ_{S→F} of the
  stored word (`Bitvector32Term::sign_cast32`, in `CType::read_cell`). Every
  load-after-store resolution that answers a load *term* (`read_cell` on a
  `LoadKind`, the materialization and stored-read checks in
  `memory_resolution.rs`, `memory_provenance.rs`, `contract_claims.rs`,
  `proof/execution.rs` and `loops.rs`) reads the cell's word, which by K1 is
  the same word, so it compares word kinds. Soundness: the read returns the
  same four bytes interpreted in F, which is C's modular conversion between
  `int` and `unsigned int`. Loads come before formatted constants.
- **K6 (equality), 2026-10-25.** A 32-bit equality is the same fact
  whichever signedness it is filed at: `Compare { UInt32, Equal }` and
  `Compare { Int32, Equal }` over the same words are one fact, so the
  e-graph, the difference graph, the fact keys and indexes, and every
  equality lookup treat them as one (`ConditionTerm::fact_format`), and the
  `uint32` format is kept for presentation. Soundness: word equality does
  not depend on the reading of the bits.
- **Printing shows σ where the signedness changes.** A value, fact or step
  holding σ prints it as `x as uint32` or `x as int32`; nothing else changes.

Maintainer direction, 2026-10-26:

- **K7 (the word of a narrow cast).** For a destination `F` of `b` = 8 or
  16 bits, `m = 2^b - 1` and `s = 2^(b-1)`, and a source `S` of at most 64
  bits, with `w = x` when `S` has at most 32 bits and `w = UInt32From64(x)`
  when it has 64:
  - `word(Cast(S -> F, x)) == w & m` when `F` is unsigned;
  - `word(Cast(S -> F, x)) == ((w & m) ^ s) - s` when `F` is signed.

  Soundness: the cast denotes `n mod 2^b` read in `F`, where `n =
  to_integer_S(x)`; by the Stage 0 invariant its word is the zero or sign
  extension of those `b` bits. `w` holds `n mod 2^32`, whose low `b` bits
  are `n mod 2^b`. `& m` zero-extends them; for `t` those bits, `(t ^ s) -
  s` is `t` when `t < s` and `t - 2^b` otherwise, with no 32-bit wrap,
  which is the sign extension. Where: the e-graph, when it interns a
  narrow cast, interns this word from the operand's class and merges the
  two (`TermClasses::narrow_cast_node`): at most five nodes and one merge,
  O(1) per cast, no scan.
- **K8 (the word of a narrow widening).** `word32` of
  `Cast(S -> F, v)` for a narrow `S` and a 32-bit `F` is `v`'s word, peeled
  as σ is; a 64-bit `F` keeps the legacy extension over that word.
  Soundness: by the Stage 0 invariant `v`'s word is `n`'s 32-bit sign or
  zero extension, which is `n`'s word in `F`.
- **Printing.** C++ and Rust print a narrow conversion as `x as uint8` or
  `x as int8` where they printed its mask arithmetic, and show the narrow
  range facts C shows. After K8 a promoted narrow value prints as
  `c as int32` where it is at rest, as σ does; it is shown, not hidden.

Maintainer direction, 2026-10-26 (syntax):

- **Click casts are written `e as T`.** An integer target is bare,
  `x as uint32`; a pointer target is parenthesized, `p as (uint8 *)`,
  `p as (struct node *)`. A Rust source's sidecar also writes Rust's scalar
  names. The C form `(T) e` is refused in Click text ("write `e as T`");
  C source keeps C's casts. Reasons:
  - it reads in order: the operand, then what it becomes, so a chain
    `x as int32 as uint64` reads left to right;
  - no precedence trap: `as` binds looser than every unary operator and
    tighter than every binary one, so `-(x as int32)` and `-x as int32` are
    visibly different, where the C form hid which one was meant;
  - it is distinct from C: a Click cast is a specification's conversion,
    with Click's rules (a checked conversion is `to_int32(e)`), and a
    spelling of its own keeps it from reading as the C conversion of the
    program's source;
  - pointer targets are parenthesized because `p as uint8 * q` would leave
    the `*` ambiguous between the type and a multiplication.

  The migration was mechanical: the parser recorded every C-form cast it
  read, a rewrite applied each as `e as T`, and every rewritten source
  parsed back to the same file (its position-free form compared by hash). The
  hash-pinned historical Rust proofs (`design/charon-trial/parity.json`) were
  respelled once, with their old tactic names, signatures and citations, and
  re-pinned; each is byte-identical to what the retired reading adapter
  produced from its original.

- **Integer termination measures (2026-10-26).** Every `decreases` component
  is an Integer position, including pure functions, recursive C contracts,
  and lexicographic loop measures. Arithmetic observes each machine operand
  before operating, so `decreases a + b;` owes no overflow obligation.
  Resource-application measures keep their existing meaning.

Maintainer direction, 2026-10-26 (Stage 5), superseding the 2026-10-21
entry "`bool` is logical; C's `_Bool` is an integer":

- **One logical sort, `Bool`, for every language.** Click writes it
  `Bool`, as it writes `Integer`. C `_Bool` and `bool` (C99 to C23), C++
  `bool` and Rust `bool` all denote it; there is no {0, 1} integer format.
  Function heads keep their language's names (`bool` or `_Bool` in C,
  interchangeably; `bool` in C++ and Rust); in Click's own code a lowercase
  `bool` is an error that suggests `Bool`.
- **`Bool` to integer is a cast.** C and C++ promotion, arithmetic, a
  comparison with an integer and indexing, and Rust `b as i32`, build the
  conversion-table node `Cast(Bool -> F, b)` (`BoolCast`, merged into
  `Cast` in Stage 3), printed `b as int32`. Rule C1: its value is 1 when `b`
  holds and 0 otherwise, so `b as F == 1` exactly when `b`, `b as F == 0`
  exactly when `not b`, and `0 <= b as F <= 1` with
  `b as F == 0 or b as F == 1`; the e-graph keeps the cast linked with `b`.
- **Integer to `Bool` is the comparison** `x != 0` (a null test for a
  pointer), with no node. C `if (n)` is unchanged.
- **The byte rule.** A `bool` cell is one byte: a store writes 1 or 0, a
  read of byte `b` is `b != 0` and requires `b` to be 0 or 1. A value this
  session stored meets it by construction, a read through a reference
  meets it by the type's validity invariant, and a byte view of a `bool`
  cell or a write at another kind is refused.
- **Logic rules.** L-If: `if c { a } else { b }` is the case split
  `(c and a) or (not c and b)`, opened only on demand. L-Eq: a true
  `a == b` merges the two values' classes; a false one contradicts the
  merge. L-Unfold: unfolding a `-> Bool` function's application files
  `application == body`.
- **Refusals.** A `Bool` compared with an integer, ordered, or used in
  arithmetic, implicit promotion in a contract included, is an error that
  suggests `b as int32` or `true`/`false`. A census of the corpus comes
  before the switch.
- **Rust** comparisons and connectives are `Bool` values with no path
  split. Generic instantiation at `Bool` is supported only if the census
  needs it. Teaching `solve` that `b or not b` is a separate proposal.

Maintainer direction, 2026-10-28 (Stage 5 complete), superseding the
2026-10-21 entry "`bool` is logical; C's `_Bool` is an integer" as built,
and refining the 2026-10-26 entry:

- **Every `bool` is `Bool`.** C `_Bool`/`bool`, C++ `bool` and Rust `bool`
  values are the kernel's logical sort, carried as C1's cast to `uint8`.
  There is no {0, 1} integer format; `Bool` to integer is the cast
  `b as F` (C1), and integer to `Bool` is `x != 0`.
- **The byte rule is the read `byte != 0`** over the ordinary byte load,
  with no separate load form. Every producer of a `bool` byte writes C1's
  byte, and every other writer is refused, so the byte is 0 or 1.
- **Rust needs no path split** for comparisons and connectives (D5).
- **`&bool`, `&[bool]` and C `bool *` stay unsupported** until the shared
  bool-cell pointer type in the Stage 5 follow-ups is designed and
  approved.

Maintainer direction, 2026-10-29 (every format its own nodes), superseding
the word identity of K1, K2, K5's naming, K6 and K8 as each step lands:

- **Lowering keeps a term's structure** (`docs/internals/spellability.md`,
  "Lowering is structural"). Every format has its own nodes: `+` at
  `uint32` is `Binary { Add, UInt32 }` over `uint32` operands, and likewise
  at 8, 16 and 64 bits; constants keep their format. A cast appears only
  where the source writes one or the language's semantics insert one. C's
  narrow arithmetic stays promote, operate, cast, which is its structure;
  Rust's narrow arithmetic and specification arithmetic at a narrow type
  become native narrow nodes.
- **Cross-format relations are e-graph facts, each O(1) per firing, with no
  scan:**
  - R0: σ's inverse, `σ_{F→S}(σ_{S→F}(x)) = x` as a class, so equality
    carries across σ by congruence.
  - R-dist: for a cast `C` to a format no wider than the operator's,
    `C(a op b) == C(a) op C(b)` for `+ - * & | ^`, `C(~a) == ~C(a)`, and
    `C(a << k) == C(a) << k` when `k` is below the destination's width.
    The same-width case is σ's distribution (R1).
  - R-comp: a cast of a widening, or a truncation of a truncation, is one
    cast. R-dist and R-comp together give the truncation of promoted
    arithmetic (R2), with constants and mixed operand formats.
  - K7′: a narrow cast's widening equals its operand's mask (K7 restated).
  - R-mem: reads of the same bytes at two signednesses are related by σ.
  - Division, remainder, right shift and comparisons keep their own signed
    and unsigned nodes.
- **K1, K2, K6 and K8 are deleted; K3 and K4 are restated** to read σ as an
  explicit node; **K5's reinterpretation is kept** as memory semantics and
  its naming deleted; **K7 is restated** as K7′.
- Decisions G1 to G11:
  - G1: typed index coordinates; if PR 5 cannot take them, the word stays
    as a named address-only exception.
  - G2: specification arithmetic at a narrow type is the native node.
  - G3: R-dist with R-comp is the general form of R2.
  - G4: Rust `+ - * & | ^ ! <<` native now; `/ % >>` and comparisons later
    if needed.
  - G5: each read its own load, with R-mem; 32 bits now, bytes later.
  - G6: R-dist fires on class merges, not only on syntax.
  - G7: pending the audit: what a `signed_int32` certificate does with a
    `uint32` operator.
  - G8: traces name the signedness, `read<UInt32>` and `read<Int32>`.
  - G9: one formatted `Constant { format, bits }`, in a later
    pure-reordering PR.
  - G10: spellings print as written: `((a as int32) + 1) as uint32` raises
    as itself.
  - G11: the Charon-trial proofs are re-pinned when they change.
