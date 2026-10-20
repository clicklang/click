# Design a consistent standard library

Priority: P2.

Soundness: not soundness. This issue reorganizes and fills in library
content. The prelude's theorems are already checked by
`verify_standard_library`, and its five `extern` contracts are already
listed as assumptions in [trust](../docs/concepts/trust.md). Moving a
declaration must not change what it means. A primitive or `extern` contract
must not lose its trust listing or its checked use.

This issue also tracks Integer-default specification arithmetic
([below](#integer-default-specification-arithmetic)), which decides which
library lemmas survive. That work adds kernel rules; each one carries its
own soundness argument and regressions.

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
- **Machine-integer bridges.** 110 of the 162 theorems are width-specific
  lemmas such as `int32_less_equal_transitive` and
  `uint64_subtract_to_integer`.

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

- `count` and `permutation` are monomorphic over `int32[]` with `int32`
  bounds, even though `List<T>` shows that the library supports generics.
- `allocation(base: int32*, bytes: int32)` states its byte count as `int32`,
  while `malloc` takes a `size_t`.
- Names follow several patterns (`int32_less_than_implies_less_equal`,
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
   library by name. The C++ catalog and Rust core contracts are already
   generated per use, for the element types a call instantiates, so they
   stay generated rather than becoming `library/cpp/` and `library/rust/`
   files; a templated library file needs a generic mechanism Click does not
   have yet.
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
   - Next: `machine_integer` and `integer`, which wait on the
     Integer-default arithmetic decision.
6. Document the primitives in the language reference, and describe the
   library per module in the reference.
7. Apply the consistency rules below: generic `count` and `permutation`,
   `size_t` sizes for `allocation`, and the width-lemma families.

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


Today: `+` in a specification is the C operation and is partial
(`docs/reference/language/index.md`, "an int32 fold's `+` is partial in
specifications"). Proofs bridge with `to_integer`, width-specific lemmas
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
from the other. Step 2 has
started: `arithmetic "integer";` opts a file into the rule, as a migration
switch removed when the default flips, and the kernel decides Integer
comparisons of machine observations through their native comparisons.
Under the directive, `bounded-pool`'s `pool_init` verifies with its bridge
lemmas removed; the next blocker is population counts, which are still
`int32` machine sums. Step 3 has started: `auto` proves that an in-range
machine `+` or `-` is the Integer operation (`integer_operation_identity`),
using native comparisons as Integer facts and machine type ranges, so
`ensures result == x - 1;` verifies from `requires 1 <= x;` with no bridge
lemma. Count comparisons widen under the directive, `simp` selects Integer
equalities as rewrites, and an Integer equality over 32-bit observations files
its wrapped word equality for built-in checks. `auto` reads native bounds
such as the consumed-member `count >= 1`, and signed definedness facts, as
Integer facts, proves a machine comparison through its Integer reading, and
cites callee postconditions at their call sites; a population's entry count
and any unwritten observation are spelled from the proof's state. A count is
read as an ordinary `int32` observation (an earlier exact view of count sums
was removed: it read a count differently from the same value passed as an
argument). `examples/bounded-pool` now uses the directive: all eleven
functions verify with the five helper theorems and both library imports
removed, the sidecar falls from 437 to 304 lines, and verification takes
about 4 s instead of 2.5 s. `rust-byte-sum` and `rust-iterators` also use the
directive, and so do 98 other example sidecars, `refcount`, `pcg`, the
`owned-*` examples and eight Rust examples among them. Some needed small
language support: an imported `-> Integer` function's result reads as an
Integer operand; arithmetic on a pointer parameter (of a C function or a
theorem), an `address(p)`, or a floating-point value keeps its C meaning,
which the tagged parent words of the `rbtree` insert proofs and
`jsonc-numeric`'s `double` scaling need; a contract `let` of a C value is a
machine operand; and unsigned wraparound is written with the
`machine_integer` wrapping functions (`uint64_wrapping_mul`), as `pcg` does.
Migrated proofs mostly shrink: bridge-lemma chains become one `auto()` step.
`auto` does not yet find every identity a proof needs: a nested sum
(`a + b + c`) needs its inner `to_integer(a + b) == to_integer(a) +
to_integer(b)` stated, and a conversion identity such as
`to_integer((uint32)p[0]) == to_integer(p[0])` needs an explicit
`integer_cast_identity` certificate.
Still to migrate: `arena` (loop measures over machine differences become
Integer measures), `byte-representation` (the conversion identity above),
the `rbtree-augmented` files (which import the arithmetic module together),
`jsonc-refcount`'s `inc_ref_count` (verifies, but over the 5,000-unit budget
`each_sidecar_spends_its_own_work_budget` gives it), and six Rust examples.
A Rust example migrates with its archived Charon-trial copy, which it must
match; the directive goes at the end of the file so the source positions
its Rust tests pin stay put.
Next: those migrations, then the flip.

Sequencing with the library: most of the 110 width lemmas exist only to
bridge machine arithmetic, so once the default flips they are deleted rather
than completed, and only the families that remain are completed. The
`machine_integer` and `integer` renames follow that deletion, so the rename
does not touch lemmas about to disappear.

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

## Intended regression

- A fixture that applies the same comparison and `to_integer` lemma family
  at every supported width, so a missing width fails the gate.
- `mdtests/stdlib_list*.md`-style positive and negative clients for a
  generic `permutation` over a non-`int32` element type, such as a `uint8`
  byte buffer.
- An `allocation` client whose byte count comes from a `size_t` expression,
  with no narrowing to `int32`.
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
  above.
- `count` and `permutation` are generic, or their restriction is documented
  as a kernel limit.
- `allocation` and other library sizes use `size_t`.
- Every library name follows the documented scheme.
- Existing examples and mdtests verify unchanged, apart from mechanical
  renames and import lines.
