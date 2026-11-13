# Design a consistent standard library

Priority: P2.

Soundness: not soundness. This issue reorganizes and fills in library
content. The library's theorems are checked by
`verify_standard_library`, which the gate runs
(`standard_library_theorems_are_proved_by_their_own_entry_point`), and its
five `extern` contracts are listed as assumptions in
[trust](../docs/concepts/trust.md). Moving a
declaration must not change what it means. A primitive or `extern` contract
must not lose its trust listing or its checked use.

This issue also tracks Integer-default specification arithmetic
([below](#integer-default-specification-arithmetic)), which decides which
library lemmas survive. That work adds kernel rules; each one carries its
own soundness argument and regressions.

## Status (2026-11-12)

Done: delivery steps 1 to 4, the qualified-name steps of step 5 except
generic width-free names, step 6, and the generic `permutation::count` and
`size_t` `allocation` byte counts of step 7; Integer-default specification arithmetic; machine-integer Stages 0
to 3, and Stage 4's front ends; Rust names for the lemmas a Rust proof
applies; the product-identity, `<=`-and-`!=` and round-trip width gaps
(2026-11-12). The library's own
proof check runs in the gate. Of the library's 147 theorems, 111 have checked proofs and 36 are
kernel standard theorems.

Open:

- One convention for the language library models: where the C library,
  allocator, `snprintf`, C++ catalog and Rust core contracts are stated and
  how they are reported ([Layers](#layers)).
- The fact-dependent integer lowerings
  ([below](#fact-dependent-integer-lowerings)).
- The follow-ups from the Integer-default flip
  ([below](#integer-default-specification-arithmetic)).

## Motivation

Click's library was `stdlib/prelude.click`, one 1,661-line file loaded
implicitly into every sidecar. Step 1 below split it into `library/`
modules without changing any declaration. Nobody designed it as a library.
It grew one declaration at a time, as each proof needed something, and it
mixes four kinds of declaration that have different meanings and different
trust:

- **Verifier primitives.** `mutex_guard`, `mutex_live`, `mutex_use`,
  `publisher`, `subscriber`, `authority` and `allocation` are
  `abstract resource` declarations. The kernel gives them their meaning (for
  example `ResourceAlgebra::ALLOCATION_RESOURCE_NAME`), so they look like
  library declarations but cannot be implemented in Click.
  `extern __click_constant_p_unknown` is the value of the C builtin
  `__builtin_constant_p`, not a library function.
- **C library contracts.** `memcpy`, `memcmp`, `memset` and `strlen` are
  assumed `extern` contracts in the prelude. The allocator family
  (`malloc`, `calloc`, `realloc`, `free`) is instead built into the C front
  end (`src/languages/c/syntax.rs`, `src/surface/verification.rs`). The C++
  catalog for `std::span` and `std::as_writable_bytes` is generated from
  `src/languages/cpp/standard_library.rs`. So library models live in three
  places, and each place has its own conventions.
- **Mathematical library.** `Nat`, `List<T>` and their theorems are generic
  and reasonably organized.
- **Machine-integer bridges.** At filing, 110 of the 162 theorems were
  width-specific lemmas such as `int32_less_equal_transitive` and
  `uint64_subtract_to_integer`. Today 63 of the 147 theorems are: 55
  width-prefixed `integer::` lemmas and the eight `integer::to_*_round_trip`
  laws. 111 of the 147 have checked proofs and 36 are kernel standard
  theorems ([trust](../docs/concepts/trust.md#the-click-library)).

The width lemmas have no consistent coverage across widths. On master at the
time of filing:

| Lemma family | Widths present |
| --- | --- |
| `less_equal_transitive`, `less_than_transitive`, `*_to_integer` comparisons, `to_integer_bounds` | `int32`, `int64`, `uint32`, `uint64` |
| `greater_equal_transitive`, `less_than_implies_less_equal`, `positive_is_nonnegative` | `int32` only |
| `less_equal_and_not_less_than_implies_equal` | `int32`, `uint64` |
| `greater_equal_implies_reversed_less_equal` | `int32`, `uint32` |
| `to_integer_less_than_implies_less_than` | `int64`, `uint64` |
| `divide_to_integer`, `multiply_to_integer` | `uint32`, `uint64` |
| increment and predecessor lemmas (fourteen forms) | mostly `int32`; a few `uint32` |
| any of the above | never `int8`, `int16`, `uint8` or `uint16` (only `integer_to_*_round_trip` covers them) |

A proof that moves from `int32` to `int64` or `uint16` therefore loses
lemmas it relied on, and the author cannot predict which ones. Other
inconsistencies:

- `count` and `permutation` were monomorphic over `int32[]` with `int32`
  bounds, even though `List<T>` shows that the library supports generics.
  Done: `permutation::count<T>` is generic over the element type;
  `permutation::permutation` stays over `int32[]`, a documented limit (step
  7 below).
- `allocation(base: int32*, bytes: int32)` states its byte count as `int32`,
  while `malloc` takes a `size_t`. Done: the byte count also accepts a
  `uint64` (step 7 below).
- Names follow several patterns (`int32_less_equal_and_not_equal_implies_less_than`,
  `uint32_less_than_implies_reversed_greater_than`,
  `integer_positive_divisor_quotient_strict_lower`), with no documented rule.
- `bytes_*` and `cstr_*` are a coherent family, but only over `uint8[]` with
  `uint64` indices.

## Violated invariant

The standard library should be a designed, documented API:

1. Each declaration belongs to a named layer (primitive, C/C++ library
   model, or specification library), and that layer determines its trust
   status.
2. Within a layer, an operation stated for one integer width or element type
   is stated for every supported width or type, or the reference documents
   why it is not.
3. Names follow one documented scheme.
4. A sidecar can see which parts of the library it uses, rather than
   receiving all of it implicitly.

Today none of these hold.

## Accepted design, 2026-10-14

These decisions were agreed with the user. Implement them; internal APIs
and file boundaries within a layer are implementation details.

### Name and location

The library is "the Click library". Its source lives in `library/`, one
module per file, replacing `stdlib/prelude.click`. "Prelude" no longer names
the whole library. "Standard library" is avoided in Click documentation,
because a sidecar sits beside C, C++ or Rust code whose own standard library
uses that name.

### Imports

A library module is imported by a `::` path rooted at `click`, mapped onto
`library/`:

```click
import click::bytes;                   // library/bytes.click
import click::c::string;               // library/c/string.click
import "../rbtree-model/model.click";  // a project file: a quoted path
```

The root is `click`, not `std`, so a library path cannot be confused with
C++'s or Rust's `std` in the code being verified. Project files keep quoted
relative paths, which already exist and are unchanged. A library module
follows the [specification-imports](specification-imports.md) rules: it is
loaded once, its names are available unqualified, conflicts are rejected,
and importing it does not run its proofs. Selective imports and qualified
names (`click::list::append`) remain deferred to that issue.

### What is implicit

- `Nat` and `List<T>`, with their functions and theorems, are available
  without an import.
- Verifier primitives are part of the language and are always available.
  These are the abstract resources `mutex_guard`, `mutex_live`,
  `mutex_use`, `publisher`, `subscriber`, `authority` and `allocation`, plus
  `__click_constant_p_unknown`.
- Every other specification module (`bytes`, `cstr`, `integer`,
  `permutation` and so on) requires an explicit `import click::...;`.

### Language library models come with the code

Library contracts for C, C++ and Rust attach to what the verified code
uses, not to sidecar imports. Including `<string.h>` brings the `memcpy`,
`memcmp`, `memset` and `strlen` contracts; `<stdlib.h>` brings the
allocator family. Using `std::span` brings its C++ catalog contracts, and
using a Rust core slice method brings its contract. The contracts are
written under `library/c/`, `library/cpp/` and `library/rust/`, with module
paths such as `click::c::string` for documentation and explicit reference.
A model's own specification dependencies (for example, `strlen` on
`cstr_at`) are imported by its model file, not by the sidecar.

### Qualified names (accepted 2026-10-14)

Qualified names are part of this issue; the user moved them here from the
deferred scope of [specification-imports](specification-imports.md).

- **Paths.** A library declaration's full name is its module path and its
  name: `click::list::append`. A full path works without an import, like a
  Rust path. After `import click::list;`, or for an implicit module, the
  module name is in scope and `list::append` names it too.
- **Selective imports.** `import click::list::{append, length};` brings bare
  names into scope.
- **Prefixes go.** Library names drop the module prefixes they carry today:
  `list_append` becomes `list::append`, `nat_add` becomes `nat::add`. Bare
  library names are no longer in scope by default, since names repeat
  across modules; a file writes a path or a selective import.
- **Clashes follow Rust.** A file's own declaration shadows a name from an
  implicit module, like Rust's prelude. A selectively imported name that
  clashes with a file declaration or with another selective import is an
  error, as Rust's explicit `use` is (E0255, E0252). A path never clashes.
  Click has no glob import.
- **Tactics and expansion.** Built-in tactics refer to library theorems by
  qualified identity, so a file theorem never takes a library theorem's
  place and library theorem names are no longer reserved. `click expand`
  writes the shortest spelling that resolves to the same declaration in the
  file: a bare name when a selective import brings it and nothing shadows
  it, otherwise `module::name` when the module is in scope, otherwise the
  full `click::` path.
- **Project files** keep quoted imports and unqualified names for now; an
  `as` alias for them is not part of this issue.

Delivery: qualified-path resolution while the old names still work; tactics
and expansion on qualified identities, lifting the reservation; selective
imports; then the rename, with a scripted migration that removes the old
names.

### Delivery order

Each step is a separate PR that leaves every example verifying:

1. Done: split `stdlib/prelude.click` into `library/` modules, all still
   loaded implicitly in the original declaration order. No meaning changes.
2. Done: resolve `import click::...;` to library modules. An import is
   checked against the module table and recorded; it selects nothing yet.
3. Done: make the non-implicit specification modules explicit. A script
   added the import lines to existing sidecars and fixtures. Until step 4,
   `c/string` stays implicit and brings `bytes` and `cstr` with it, so the
   modules that now need an import are `machine_integer`, `integer` and
   `permutation`. Built-in tactics apply library theorems by name, so proof
   checking keeps every library theorem and theorem names stay reserved;
   imports gate the declarations and theorem citations a file writes, and
   `click expand` adds the import a written-out theorem citation needs.
4. Done: attach the C library models to the code. `click::c::string` comes
   with a C declaration of, or call to, one of its functions, whether from
   `<string.h>` or the program's own prototype, since a C call binds to the
   library by name. The C++ catalog and Rust core contracts are
   generated per use, for the element types a call instantiates. Rust's
   core integer methods state their results with specification functions
   in `library/rust/`, one module per integer type, since a templated
   library file needs a generic mechanism Click does not have yet; the
   per-use `extern` contract only names them.
5. Qualified names, as described above, in small PRs:
   - Done: `click::m::name` and in-scope `m::name` resolve to the library
     declaration before parsing, and a full path brings its module.
   - Done: library theorems have qualified verifier identities. Tactics and
     kernel-checked standard theorems use them, a file theorem may share a
     library theorem's bare name, and `click expand` spells a cited library
     theorem by its bare name unless the file shadows it.
   - Done: selective imports, and the `list` rename. `click::list`
     functions, predicates and theorems have qualified identities and need
     a path or a selective import; `List` and its constructors stay bare.
     Qualifying predicates and functions with each module's rename made a
     separate identities step unnecessary.
   - Done: the `nat` rename. `nat_add` is `nat::add`, and the conversion
     laws are named for the composition they state: `nat::to_integer_zero`,
     `nat::to_integer_add`, `nat::to_nat_to_integer` and so on. `Nat` and
     the primitive `to_nat` stay bare.
   - Done: the `bytes` rename: `byte_count` is `bytes::count`, and
     `bytes_equal` and its siblings are `bytes::equal` and so on. A sidecar
     whose C string call brings the module without an import writes the
     full `click::bytes::` path. Inventory IDs of renamed modules carry the
     module, `library.function.bytes::count`, since `count` repeats in
     `permutation`.
   - Done: the `cstr` rename: `cstr_len` is `cstr::len`,
     `cstr_readable` is `cstr::readable`, and so on. The predicate that
     was `cstr` keeps its name as `cstr::cstr`, beside `cstr::len` and
     `cstr::readable`.
   - Done: the `permutation` rename: `count` and `permutation` are
     `permutation::count` and `permutation::permutation`, so a file may
     declare its own `count` or `permutation` beside a module import.
   - Done: the integer rename (machine_integer merged). Every
     `click::machine_integer` declaration moved into `click::integer`
     (maintainer, 2026-10-22), and `click::machine_integer` is removed, with
     no alias, since no public example needs the old module. The module's
     names drop the redundant `integer_` prefix:
     `integer_floor_from_remainder` is `integer::floor_from_remainder` and
     `integer_to_int32_round_trip` is `integer::to_int32_round_trip`. Width
     prefixes stay: `uint32_wrapping_add` is `integer::uint32_wrapping_add`
     and `int32_less_equal_transitive` is
     `integer::int32_less_equal_transitive`. With every library module
     qualified, no library theorem is cited by a bare name without a
     selective import.
   - Not taken (maintainer, 2026-11-09): generic width-free names
     (`uint32_wrapping_add` becoming `integer::wrapping_add`). There is no
     generic `T: intn` mechanism; the width-prefixed names stay
     ([One machine-integer design](#one-machine-integer-design)).
6. Done: document the primitives in the language reference, and describe
   the library per module in the reference. The language reference's
   "Verifier primitives" section states each primitive's declaration and
   kernel meaning under `primitive.` inventory IDs, and the documentation
   gate refuses them in the library reference. The library reference has
   one section per module and describes the three layers, as
   `library/README.md` does.
7. Apply the consistency rules below:
   - Done: generic `count`. `permutation::count<T>(p: T*, ...)` takes any
     element type (a pure-function `T*` is an array ref), with `uint8`
     clients in `mdtests/stdlib_permutation_count_over_bytes*.md`.
   - Done, as a documented limit: `permutation::permutation` stays over
     `int32[]`. Its generic form quantifies over its element type,
     `forall (x: T)`, and the parser refuses a quantifier over a type
     parameter ("quantifier type must be a concrete C, Integer, or
     algebraic type"). The library reference states the limit; a byte
     permutation is a file predicate over the generic count.
   - Done: `size_t` sizes for `allocation`. Design:
     [`design/heap-extents.md`](../design/heap-extents.md) (a tagged
     32/64-bit extent chosen by the size's C type; accepted 2026-11-10),
     stages 1 to 4. `malloc`, `calloc` and `realloc` of a symbolic
     `size_t` size proved to fit `PTRDIFF_MAX` make a 64-bit block with a
     `uint64` token and a wide range, and a sidecar states that token with a
     `uint64` byte count, so the block crosses calls
     (`mdtests/an_extern_allocator_states_a_size_t_extent.md`,
     `mdtests/a_callee_frees_a_64_bit_block_it_consumes.md`,
     `mdtests/a_bounded_size_t_calloc_count_allocates_a_zeroed_64_bit_block.md`,
     `mdtests/a_realloc_grows_a_64_bit_block_and_keeps_its_prefix.md`).
   - Done, by decision (maintainer, 2026-11-09): the width-lemma
     families are not restated over a format. The width-uniformity fixture
     checks each family at every format and has no gaps
     ([below](#width-uniformity-gaps)).

## Design

### Layers

- **Primitives.** These are the abstract resources and builtins that the
  kernel or a front end interprets. They belong to the language, not the
  library. Document them in the language reference with their kernel
  meaning, and keep them available without an import. Whether they remain
  written in Click syntax is an implementation choice. Either way, the
  library reference should no longer present them as library content.
- **Language library models.** These are the C library (`string.h` and the
  allocator family) and the C++ std catalog. Use one convention for where
  their contracts are stated and how they are reported as external
  assumptions, whether they are written in Click like the `string.h`
  externs or generated like the C++ catalog. Every model is listed in
  [trust](../docs/concepts/trust.md) and has a checked use.
- **Specification library.** These are the checked types, pure functions,
  predicates and theorems. Split them into modules (for example `nat`,
  `list`, `integer`, `bytes`, `cstr`, `permutation`) using the module
  mechanism of [specification-imports.md](specification-imports.md). This
  issue owns the split, the `click::` resolution, and what goes into each
  module.

### Consistency rules

- Each width-indexed lemma family is either complete over the supported
  widths (`int8` through `uint64`) or replaced by one generic statement.
  A checked list of families and widths keeps each family complete.
  Resolved 2026-11-09 (maintainer): neither. The library lemmas stay as
  they are for existing proofs (deleting unused ones is deferred, not
  decided); what is kept complete is the kernel's reach. The checked list
  is `FAMILIES` in `src/surface/tests/width_uniformity.rs`: each family's
  statement at every format in `machine_integer::FORMATS`, proved by the
  omitted proof with no library import, or excluded with a reason
  ([below](#width-uniformity-gaps)).
- Container and array predicates are generic over the element type where
  the kernel supports it. `permutation::count` and
  `permutation::permutation` become generic if the kernel's generic folds
  allow it; otherwise their `int32` restriction is documented as a kernel
  limit (maintainer, 2026-10-15).
- Size and index parameters of library models use the C types the real
  functions use (`size_t`), including `allocation`.
- Write the naming scheme down in `library/README.md` and apply it to every
  existing declaration, as part of the qualified-name rename above.
  Rename, rather than alias, unless a public example depends on the old
  name.

### Integer-default specification arithmetic

Moved here from the launch design review (formerly its item P2), since it
decides which library lemmas survive.


Status: done. Specification arithmetic is over `Integer` by default; the
open items below are follow-ups.

At filing: `+` in a specification was the C operation and was partial
(`docs/reference/language/index.md`, "an int32 fold's `+` is partial in
specifications"). Proofs bridged with `to_integer`, width-specific lemmas
(`int64_less_equal_transitive` and about 110 more in `library/`)
and hand-written `arithmetic_certificate` blocks: about 270 lines of
`examples/bounded-pool/bounded_pool.click` show counters do not overflow.
ACSL, Dafny and Verus specs use mathematical integers by default.

Proposed fix: specification arithmetic is over `Integer` by default; C
semantics are written explicitly where a spec means them.

Done when: decided, and if fixed, the examples shrink accordingly.

Decision: fix (maintainer, 2026-10-15). Specification arithmetic is over
`Integer` by default, with these rules:

- In a specification, `+`, `-`, `*`, unary minus and the comparisons on
  machine integers are Integer operations. A machine operand widens
  implicitly, since that loses nothing; narrowing stays explicit
  (`to_int32(z)` with its bound obligations).
- Unsigned wraparound is written explicitly, with a wrapping operation or
  `% 2^N`. The migration rewrites each unsigned specification operation into
  that form, and a proof that no wrap occurs removes it.
- Integer `/` and `%` truncate toward zero, as C and ACSL do.
- Bitwise operators and shifts stay machine-typed; their results widen when
  combined with Integer arithmetic.
- `defined(e)` remains the way a specification states C evaluation.
- One switch-over by scripted migration, not a per-file mode. A prototype
  on `examples/bounded-pool` and one unsigned-heavy example comes first, to
  measure the proof that disappears and check timing against the
  [verification efficiency contract](../docs/internals/verification-efficiency.md).

Progress: a prototype on `examples/bounded-pool` written in Integer form
shrinks the sidecar from 437 to 284 lines, and showed that built-in checks
read only machine facts. Step 1 is done: an Integer comparison of exact
machine observations is the native comparison, stated in one form (see
"One form for comparisons of observations" in
`docs/internals/mathematical-integers.md`), so resource quantities and count
definedness accept Integer premises and `assumption` closes either spelling
from the other. Step 2 is done: specification arithmetic is Integer by
default, and the `arithmetic "integer";` migration directive is refused.
Library modules under `library/` read specification arithmetic as Integer
too: each library statement that meant a C operation was respelled to say
so with exact observations, `to_integer(value + 1) <= to_integer(upper)`,
which lowers to the same native comparison its kernel axiom states. The kernel decides Integer comparisons of machine observations
through their native comparisons; for an 8- or 16-bit value that holds only
where the word is the value's extension (a narrow load or conversion), so
`examples/rust-slices`' `u8` increment verifies. Step 3 is done: `auto`
proves that an in-range machine `+` or `-` is the Integer operation
(`integer_operation_identity`, narrow types included), using native
comparisons as Integer facts and machine type ranges, so
`ensures result == x - 1;` verifies from `requires 1 <= x;` with no bridge
lemma. Count comparisons widen, `solve` selects Integer equalities as
rewrites, and an Integer equality over 32-bit observations files its wrapped
word equality for built-in checks. `auto` reads native bounds and signed
definedness facts as Integer facts, proves a machine comparison through its
Integer reading, and cites callee postconditions at their call sites; a
population's entry count and any unwritten observation are spelled from the
proof's state. A comparison keeps its C meaning when it does arithmetic on a
pointer (a parameter, a pointer-typed local or field, a pointer `result`, or
an `address(p)`) or a floating-point value. Unsigned wraparound is written
with the `click::integer` wrapping functions (`integer::uint64_wrapping_mul`).
Migrated proofs mostly shrink: bridge-lemma chains become one `auto()` step;
`bounded-pool` dropped its five helper theorems and library imports (437 to
304 lines) and `arena` about 720 lines. A native fact a proof still reasons
with is stated over exact observations, such as
`to_integer(s) <= to_integer(s + index)`, which is stored natively. A
conversion that keeps its value only under a range condition still needs an
explicit `integer_cast_identity` certificate.
Still open from the flip:
- `jsonc-refcount`'s `inc_ref_count` costs about 25,000 work units (60 ms)
  where it cost about 3,900 before the flip: each Integer postcondition
  proves an operation identity, and each identity's two range bounds are
  full solver calls. The profile budget test is retuned to that cost.
- Deleting the width lemmas nothing needs (2026-11-12) removed only
  `uint64_to_integer_bounds`, `uint64_to_integer_equal_implies_equal` and
  `int64_add_defined_by_integer_bounds`, which nothing applied. Every other
  width lemma is applied by a built-in tactic, a library proof, a kernel
  standard theorem's registration, an mdtest, an example, a Rust import
  fixture or a verified design sidecar (`design/adler32`,
  `design/concurrency-composition`, `design/concurrency-probes`,
  `design/charon-trial`). Seven were applied only by the `src/` tests that
  checked them as bridges, and were deleted with those test rows
  (2026-11-12, approved): `uint64_less_equal_to_integer`,
  `uint64_less_than_to_integer`,
  `uint64_to_integer_less_than_implies_less_than`,
  `int64_less_equal_to_integer`, `int64_less_than_to_integer`,
  `int64_greater_equal_to_integer` and `int64_to_integer_equal_implies_equal`.
  A machine comparison and the Integer comparison of its observations lower
  to one fact, so `assumption()` or `solve` reads one as the other without
  them.
- The library's respelled lemmas still state C results
  (`to_integer(value + 1)`). Restating them over a format with generic
  names is not planned (maintainer, 2026-11-09).

Sequencing with the library: most of the width lemmas exist only to
bridge machine arithmetic, so once the default flips they are deleted rather
than completed, and only the families that remain are completed. The
merge of `machine_integer` into `integer` and the rename follow that
deletion, so neither touches lemmas about to disappear.

### One machine-integer design

Accepted 2026-10-22 in [design/machine-integers.md](../design/machine-integers.md).
The kernel has no single statement of what a machine
integer of each width is. Each rule lists the widths it supports, and the
lists disagree: 292 non-test sites name a specific `MachineIntegerType`, the
term type has per-width operator, constant and conversion variants, and the
library restates the same facts per width. The design gives every width one
format, one meaning (a term of format F denotes an element of F's range), one
term and condition family, one conversion table, and rules stated once over a
format. It supersedes the 2026-10-16 wontfix rulings in
[design/typed-indices.md](../design/typed-indices.md#rulings).

It decided the width-lemma families here: a surviving family is stated once
over a format, not completed per width, and the merge into `integer` with
its rename followed its Stage 1. Revised by the maintainer on 2026-11-09:
there is no generic `T: intn` library mechanism. The kernel rules are
stated once over a format (the Stage 1 matrix), the per-width library
lemmas remain for existing proofs, and the width-uniformity fixture
(`src/surface/tests/width_uniformity.rs`) checks the families at every
format at the surface ([gaps](#width-uniformity-gaps)).

Progress: Stage 0 is done (2026-10-23). A narrow value's word is the
canonical carrier of its format, checked in debug builds, and `auto` and
`integer_cast_identity` prove 8- and 16-bit widenings without a premise
([kernel](../docs/internals/kernel.md#one-meaning-for-a-narrow-value)).
Stage 1 is done (2026-10-24) for every gap that needs no new node: the rules
are stated once over a format in `src/kernel/machine_integer/`, a per-format
matrix checks them at all ten formats, and multiplication identities and
signed operation bounds are filled
([kernel](../docs/internals/kernel.md#machine-integer-rules)). Stage 2 is
done (2026-10-24): conditions are one family,
`Compare` and `Overflows` with a format, every format has both, and the
matrix's comparison and definedness gaps are filled. The `uint32` order is
native, as the `uint64` order is; the sign-flip encoding and its
`interval_sign_bit_flip` certificate step are gone
([design](../design/machine-integers.md#stage-2-one-condition-family)).
Stage 3 is done (2026-11-04): one term family, `Binary`, `Unary`,
`Constant` and `Cast` with a format, and `Bitvector32Term` renamed
`MachineTerm`. Two of its planned items were retired by maintainer
direction: the e-graph keeps its 32-bit word operators as a reasoning-level
equivalence (`terms::word_operator`), and floats stay in the machine term
family rather than splitting into their own term type
([design](../design/machine-integers.md#stage-3-one-term-family)). Stage 4's
front-end work is done (one conversion table, no front-end width
matrices); what remains of it is this issue's library families.

### Fact-dependent integer lowerings

Found while making lowering structural (every fact must be spellable:
lowering a raised fact gives the fact back, so lowering never consults the
facts to choose a term). These three sites are integer design questions,
so they wait for this work rather than being fixed one by one. All three
are decided: the first and third are done, and the second is done by the
fact-stable rule.

- **Specification `/` and `%`.** Decided and done (option B, maintainer
  2026-11-07): specification `/` and `%` are total. A zero divisor owes
  nothing and leaves the kernel's opaque quotient (`MachineTerm::divide`,
  the Integer `TruncatingQuotient`), a fixed but unspecified value that only
  congruence relates; every quotient or remainder bound by a symbolic
  divisor asks for a nonzero divisor. Signed `MIN / -1` still owes its
  no-overflow condition, as `+`, `-` and `*` do; `defined(a / b)` still
  states C's definedness; `truncating_quotient` and `truncating_remainder`
  still require a nonzero divisor; and executed C and Rust `/` keep their
  undefined-behavior and panic checks
  ([mathematical integers](../docs/internals/mathematical-integers.md#exact-operations-and-definedness)).
  Choosing a value for `x / 0` later remains possible, since it only adds
  facts. The option form (`checked_div(a, b) == Some(result)`) was not
  taken.
- **Byte offset restrided to an element index**
  (`byte_stride_index`, `src/kernel/eval/operators.rs`). Done
  (2026-11-13), decided by the fact-stable rule: lowering keeps the written
  byte offset `i * K` at stride one, and checking relates it to element `i`
  at stride `K`. Before, the displacement became the element index whenever
  the facts decided `signed_multiply_overflows(i, K)` false, so the pointer
  term's shape depended on the facts. Now the pointer arithmetic records
  `defined(i * K)` when the facts decide it, the equality graph merges the
  two offsets under that fact, and memory resolution asks the same question
  within the statement that forms the offset
  ([equality closure](../docs/internals/equality-closure.md),
  [spellability](../docs/internals/spellability.md#lowering-is-fact-stable)).
- **Unsigned index spelling** (`pointer_index_term`, same file). Done in
  5854abb33 (2026-10-30): `pointer_index_term` no longer takes facts, and a
  `uint32` index is always the zero-extended 64-bit `uint64_from_32(x)`.
  Before, a `uint32` index whose facts proved `0 <= x as int32` became the
  `int32` index `sign_cast32(x)`. Range checking relates the word to its
  widening through the maintained order graph, the speller writes `a[i]`
  back, and the unsigned loop proofs passed unchanged
  ([spellability](../docs/internals/spellability.md#lowering-is-fact-stable)).

### Naming decisions (maintainer, 2026-10-15)

- The predicate that was `cstr` stays `cstr::cstr`.
- A module that C code brings without an import, such as `click::bytes`
  through a C string call, is not in scope by its short name; such a file
  writes the full `click::` path, or imports the module.


### Rust names for the surviving lemmas

Moved here from the launch design review (formerly its item L4, "Rust and C++
specs still read like C"; decision: fix, maintainer, 2026-10-13). Rust
sidecars already write Rust types, `as`, `bool`, Rust literal spellings and
slice parameters in pure functions. What remains is the shared lemma
library: its lemmas are named by C types (`uint64_less_than_to_integer`), so
a Rust proof applies C-spelled lemmas. Give the lemmas a Rust proof applies
Rust-spelled names or aliases once Integer-default specification arithmetic
settles which lemmas survive; naming the width lemmas first would name
lemmas that are about to be removed. The archived Charon-trial sidecars under
`design/charon-trial` keep the C spellings they were written in.

Done when the lemmas a Rust example applies have Rust spellings and a Rust
fixture applies them by those names.

Status: done (2026-11-12). Three lemmas are applied by Rust proofs, and each
has a Rust-named wrapper theorem in the module of its operand type, proved by
applying the C-named lemma (not a kernel standard theorem):
`u32::multiply_to_integer` (`integer::uint32_multiply_to_integer`),
`usize::multiply_to_integer` (`integer::uint64_multiply_to_integer`) and
`usize::product_bound_from_division`
(`integer::uint64_product_bound_from_division`). `examples/rust-unsigned`
and `rust_usize_arithmetic_casts_and_expansion_verify` in
`tests/rust_import.rs` apply them by those names, and
`mdtests/stdlib_every_symbol.md` uses each. Library theorems are qualified
per module, so two modules may declare one bare name
(`is_qualified_declaration` in `src/surface/names.rs`). The verified
`design/adler32/project/adler2` sidecar keeps its C spellings
(`integer::uint64_divide_to_integer`, `integer::uint64_add_to_integer` and
others, which have no Rust wrapper), as do the archived `design/charon-trial` sidecars.

## Width-uniformity gaps

`src/surface/tests/width_uniformity.rs` states 38 families at the ten
formats of `machine_integer::FORMATS` (`int8` to `uint128`), and the
omitted proof closes all 280 statements that apply. Division and
remainder by a symbolic divisor have no kernel rule (they stay kernel
standard theorems, maintainer decision) and are not families there;
neither are the byte-packing laws (`uint32_pack_uint16_*`,
`uint32_unpack_uint16_*`, `uint64_*_uint16_*`, `uint32_from_le_bytes`),
which state a field layout of particular widths. The product identity,
`<=`-and-`!=` and round-trip gaps closed on 2026-11-12: `solve` plans a
product's bounds by `integer_product_bounds`, the Integer certificate's
`less_than_from_not_equal` makes a bound strict by a disequality, and
`integer_cast_identity` reads `to_integer(to_T(z))` as `z` under `T`'s
range, so the eight `to_*_round_trip` laws are proved. The wrapping
difference order (`difference_decreases_after_increment`) left the list on
2026-11-13 (maintainer): its `uint32` form is the library axiom that one
loop-measure closure applies, and no other width has a client, so the
120-line proof and the per-width family went.

Excluded pairs are statements that do not apply: an operation at 128 bits
(no operator node), `defined(...)` outside `int32` and `int64` (C has no
undefined arithmetic there), a signed-only law at an unsigned format and
an unsigned-only law at a signed one, where each is false.

## Intended regression

- A fixture that applies the same comparison and `to_integer` lemma family
  at every supported width, so a missing width fails the gate. Done:
  `width_family_representatives_close_at_every_format` proves the
  `<=`-to-`to_integer` bridge and the range at every format in the gate,
  `every_format_is_tested_and_family_names_are_unique` fails on a
  format with no test, and the
  nightly `width_families_close_at_*` tests prove every family
  (`src/surface/tests/width_uniformity.rs`).
- `mdtests/stdlib_list*.md`-style positive and negative clients for a
  generic `permutation` over a non-`int32` element type, such as a `uint8`
  byte buffer. Done for the generic count:
  `mdtests/stdlib_permutation_count_over_bytes.md` and its `_after_a_store`
  sibling (positive), `stdlib_permutation_count_rejects_mixed_element_types.md`
  (negative), and the nightly `_over_bytes_rejects_overwrite` refusal.
- An `allocation` client whose byte count comes from a `size_t` expression,
  with no narrowing to `int32`. Done:
  `mdtests/a_callee_frees_a_64_bit_block_it_consumes.md` and
  `mdtests/an_extern_allocator_states_a_size_t_extent.md`.
- `mdtests/stdlib_every_symbol.md` and `docs/reference/inventory.toml` stay
  complete across the reorganization. The documentation gate already
  enforces this.

## Acceptance criteria

- The library reference and `library/README.md` describe the three layers.
  Every declaration is in exactly one layer, and primitives are documented
  in the language reference.
- C library and C++ catalog models follow one documented convention and
  are listed in [trust](../docs/concepts/trust.md).
- The library is split into `library/` modules. `Nat`, `List` and the
  primitives are implicit; every other specification module is imported with
  `import click::...;`, so a sidecar's imports show which modules it uses.
- C, C++ and Rust library contracts arrive with the header or module the
  verified code uses.
- Specification arithmetic is over `Integer` by default, the
  `arithmetic "integer";` migration switch is gone, and the examples have
  shrunk accordingly.
- The checked list of width-lemma families has no gaps, and the decision on
  each family follows the Integer-default arithmetic decision described
  above. The list exists (`FAMILIES` in
  `src/surface/tests/width_uniformity.rs`) and has no gaps
  ([Width-uniformity gaps](#width-uniformity-gaps)).
- ~~If [design/machine-integers.md](../design/machine-integers.md) is
  accepted, each surviving width-lemma family is one statement over a
  machine-integer format.~~ Withdrawn (maintainer, 2026-11-09): no generic
  mechanism; the kernel rules are stated once over a format and the
  fixture guards width uniformity.
- `count` and `permutation` are generic, or their restriction is documented
  as a kernel limit.
- `allocation` and other library sizes use `size_t`.
- Every library name follows the documented scheme.
- Existing examples and mdtests verify unchanged, apart from mechanical
  renames and import lines.
