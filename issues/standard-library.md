# Design a consistent standard library

Priority: P2.

Soundness: not soundness. This issue reorganizes and fills in library
content. The prelude's theorems are already checked by
`verify_standard_library`, and its five `extern` contracts are already
listed as assumptions in [trust](../docs/concepts/trust.md). Moving a
declaration must not change what it means. A primitive or `extern` contract
must not lose its trust listing or its checked use.

## Motivation

Click's standard library today is `stdlib/prelude.click`, one 1,661-line
file loaded implicitly into every sidecar. Nobody designed it as a library.
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
  mechanism of [specification-imports.md](specification-imports.md). That
  issue already owns the split mechanism. This issue owns what goes into each
  module and the consistency rules.

### Consistency rules

- Each width-indexed lemma family is either complete over the supported
  widths (`int8` through `uint64`) or replaced by one generic statement.
  A checked list of families and widths keeps each family complete.
- Container and array predicates are generic over the element type where
  the kernel supports it. `count` and `permutation` become generic, or their
  `int32` restriction is documented as a kernel limit.
- Size and index parameters of library models use the C types the real
  functions use (`size_t`), including `allocation`.
- Write the naming scheme down in `stdlib/README.md` and apply it to every
  existing declaration. Rename, rather than alias, unless a public example
  depends on the old name.

### Sequencing with Integer-default specification arithmetic

[design-review.md](design-review.md) P2 and [smt-auto.md](smt-auto.md)
stage 4 propose that specification arithmetic use `Integer` by default. If
that lands, most of the 110 width lemmas exist only to bridge machine
arithmetic and can be deleted rather than completed. Do the layering, the
generic predicates, the `allocation` signature and the naming scheme first.
Decide the width-lemma families only after that arithmetic decision is
made. If it is decided against, complete the families. If it lands, delete
the families it makes unnecessary and complete only the ones that remain.

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

- The library reference and `stdlib/README.md` describe the three layers.
  Every declaration is in exactly one layer, and primitives are documented
  in the language reference.
- C library and C++ catalog models follow one documented convention and
  are listed in [trust](../docs/concepts/trust.md).
- The specification library is split into modules once
  [specification-imports.md](specification-imports.md) delivers that
  mechanism. A sidecar's imports show which modules it uses.
- The checked list of width-lemma families has no gaps, and the decision on
  each family follows the Integer-default arithmetic decision described
  above.
- `count` and `permutation` are generic, or their restriction is documented
  as a kernel limit.
- `allocation` and other library sizes use `size_t`.
- Every library name follows the documented scheme.
- Existing examples and mdtests verify unchanged, apart from mechanical
  renames and import lines.
