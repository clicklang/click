# An index keeps its type until it is an offset

Status: direction accepted on 2026-10-08. Stage 1 and the kernel half of
stage 3 are built. This document states
the design, what a survey of the kernel found, and the order to build it in.
The site counts come from one read-only survey of `src/kernel` by text
search; they size the work and are not an audit.

## The problem

A place in a contract is `p[i]` or a range `p[lo..hi]`. Every index and
bound is forced through signed 32 bits before it reaches memory. A C `int`
index fits that. A C `size_t` and a Rust `usize` do not, so their contracts
cast at each use and state the bound that makes the cast exact:

```click
requires length <= 2147483647u64;
views bytes[0..(int32)length];
ensures result == bytes[(int32)index];
```

That is not C's rule. In C, `p[i]` converts `i` to a pointer-sized offset:
an `int` is sign-extended and a `size_t` is used as it is. The 32-bit limit
belongs to Click's representation of a range. It happens to match C's
commonest case and shows as bookkeeping everywhere else.

## The design

An index keeps its own integer type until the moment it becomes an offset,
and each type converts in its own exact way.

| Written | Index type | Becomes an offset by |
|---|---|---|
| C `p[i]`, `int i` | `int32` | sign extension, as C converts to `ptrdiff_t` |
| C `p[n]`, `size_t n` | `uint64` | its value |
| Rust `bytes[index]` | `usize` | its value |
| Rust `bytes[0..bytes.len()]` | `usize` | its value |

No cast is written, because nothing is narrowed. The one bound left is that
an object is at most `isize::MAX` bytes, which C and Rust both guarantee and
the memory model supplies. Each language indexes with the types it has; the
kernel has one notion underneath, an offset from a base.

## What the kernel has today

The offset layer is already typed. `PointerOffsetTerm`
(`src/kernel/primitives.rs`) is an exact integer held in `i64`, with
`Int32Scaled` and `Int64Scaled { unsigned }` forms, and
`Pointer::offset_by_typed_elements` builds the right one. Its only
production caller is C pointer arithmetic in a function body
(`src/kernel/eval/operators.rs`), so a body's `bytes[index]` with a `size_t`
index already forms a wide offset.

Three things are still 32-bit.

- **Range bounds.** `CMemoryRange` holds `start` and `end` as untyped
  `Bitvector32Term`s, and every reader takes them as signed 32-bit. A 64-bit
  bound is refused where a range is lowered ("segment start did not evaluate
  to int32"), in eight checks across `src/surface/lowering`,
  `src/surface/checking` and `src/kernel/loops.rs`. About 230 sites build a
  range and about 400 read a bound.
- **Object extent.** The byte count of a range is a `u32`
  (`memory_range_byte_count`, `memory_range_element_count_limit`), and
  `byte_normalized_memory_range` stores that count as a range bound.
  Overlap, loans and covering across element widths rest on it. About 50
  sites.
- **Order reasoning.** `PureFactContext::decide` has a 64-bit arm, but the
  transitive order walk and the bounds index match the 32-bit comparisons
  only. `0 <= i < n` over `uint64` is decided when stated or reducible to
  constants; chains and `i + 1 <= n` are weaker than for `int32`.

The first two are why a contract casts. The third is why removing the cast
alone would make existing proofs harder.

## How to build it

Keep the bound terms as they are. Give `CMemoryRange` one field, the index
kind: `Int32`, `Int64` or `UInt64`. Then:

- convert a bound to an offset through `offset_by_typed_elements`, at
  `byte_footprint` and the 48 `offset_by_elements` sites;
- recover an index from an offset with its kind
  (`element_index_from_offset`, `element_index_from_base`);
- choose the comparison by kind in the five places that order bounds: the
  overlap check, loop-effect containment, `pointer_access_in_range`, and the
  two symbolic index walks;
- accept a typed bound at the eight lowering checks.

A range's kind defaults to `Int32`, so the constructors that exist do not
change meaning.

### Stage 1. Typed bounds, with the 32-bit cap kept

A bound or index of any integer type is accepted and converted to the
32-bit index a place takes. The requirement that it fits stays. Casts
disappear from C and Rust contracts alike. Contracts still state
`requires n <= 2147483647`.

Built 2026-10-08, by a smaller route than the `kind` field above. A 64-bit
bound or index is converted where it meets the place, as the cast
`(int32)n` converts it, so every term downstream is the one an explicit cast
gives and no reader of a range changes:

- a range bound of any form, where the surface lowers a segment
  (`lower_resource_segment_with_values`) and where the kernel evaluates one
  (`evaluate_loop_effect_segment` and its sibling in `src/kernel/loops.rs`);
- an indexed read, for a 64-bit parameter written alone, in the parser
  (`wide_index_params`). Any other 64-bit index expression still takes the
  cast, because the parser does not type expressions.

The kernel's cast already owes an "int32 narrowing upper bound" obligation,
so a contract whose requirements do not show the bound fits is refused at
setup; the refusal now says which requirement to state.

What looked like a gap in this stage belongs to stage 3. A 64-bit index
expression that is not a lone parameter, `bytes[index + 1]`, still takes the
cast in a contract. Converting it in the parser was tried on 2026-10-08 and
dropped, because the C is the obstacle and not the contract: for

```c
unsigned char next(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index + 1];
}
```

with `requires length <= 2147483647; requires index + 1 < length; views
bytes[0..length];`, the body's own read is refused, "missing resource fact
`views bytes[(truncate32(index) + 1)]`", whatever the contract's
postcondition says. The kernel does not carry `index + 1 < length` over
64-bit terms to the 32-bit index of the range. That is the order reasoning
of stage 3, and it is the first thing a real `size_t` loop will hit.

### Stage 2. The extent is `isize::MAX`

The byte count becomes 64-bit with the limit `isize::MAX / width`, and the
contracts drop the bound. This cannot be done piece by piece: the `u32`
count is itself a range bound and is read by overlap, loans and
cross-width covering together. It also needs the exact form of the
base-delta addition in the overlap check and loop containment, which adds
modulo 2^32 today.

### Stage 3. Order reasoning for 64-bit terms

The order walk, its memo and the bounds index reach the 64-bit comparisons.
Stage 1 can land before this, because a contract may still cast where a
proof needs the 32-bit reasoning. Stage 2 should not: with the bound gone, a
`usize` proof has only the 64-bit route.

The kernel half was built on 2026-10-08, in
`src/kernel/assumptions/condition_reasoning/order_paths.rs`:

- `wide_order_chain` walks the unsigned or the signed 64-bit order index
  from one end of a question to the other. It decides transitivity, a
  constant bound reached through a chain, `a <= b` with `a != b`, and
  refutes by the reversed chain. A literal is an end of a chain and never
  a step, so a question costs work in its own chain and not in the facts
  that share a constant with it; the scaling test holds both.
- The rule that lifts a truncated comparison to its 64-bit form reads
  `(int32)a + c` as the truncation of `a + c`. Truncation commutes with
  addition, so this is exact, and the range check is made on the sum.
- A signed 64-bit index is admitted where its value is proved to lie in
  `0..=INT_MAX` (`int64_index_fits_int32`). It was refused outright.

These make a C operation in range. A goal in a proof is a separate matter,
because a tactic builds a kernel theorem for each step it takes. Order
chains have theirs: `uint64_lt_transitive`, `uint64_le_transitive`,
`uint64_lt_le_transitive`, `uint64_le_lt_transitive` and the same four for
`int64` (`prove_wide_order_transitive`). Linear arithmetic does not:
`arithmetic() using` proves a linear `uint64` order goal through those
bridges (`src/surface/proof/wide_arithmetic.rs`): it writes the steps a
proof would write by hand and adds no rule to the kernel. A `size_t` loop
invariant (`i + 2 <= length` from `i + 1 < length`) is one step.

## Risks

- **Kinds mixed on one block.** Two ranges of different kinds compared with
  one operator. The kernel has had this class of bug: `p[-1..0]` read as
  index 4294967295 (`memory_range_covers_with_exact_index`). Every ordered
  comparison of bounds has to name its kind, and a comparison across kinds
  has to convert both to offsets first.
- **`uint64` above `i64::MAX`.** `scale_int64` folds a constant only when it
  fits `i64`; the symbolic case is unguarded. The extent limit has to bound
  the index before it is scaled.
- **Low-word facts.** A 32-bit fact can pin only the low word of a 64-bit
  term (`src/kernel/reasoning/path_facts.rs`). A typed bound must not be
  resolved from one.
- **Constant readers.** `constant_range_extent` and
  `memory_range_in_element_width` read a constant bound `as i32`.
- **Struct-cell scaling** multiplies a bound in `int32` in the parser.

## Efficiency

A range is on the verifier's hot path, and
`docs/internals/verification-efficiency.md` asks for deterministic scaling
regressions over several input sizes before a representation change. Three
of its rules bear on this one: ranges are indexed by the root of their base,
`Pointer` orders every `S + c` of one anchor by `c`, and terms used as cache
keys need stable identities. The kind field has to keep all three. The
existing regressions to extend are the symbolic-index, stores-beside-ranges
and range-membership tests in `src/surface/tests/scaling_tests.rs`,
`src/kernel/tests/memory_scaling_tests.rs` and
`src/kernel/tests/resource_scaling_tests.rs`.

## Order of work

1. Stage 1 in the kernel, behind the existing surface: a typed bound is
   accepted, with regressions for each kind and for two kinds on one block.
2. Stage 1 at the surface: C and Rust sidecars drop the casts. The Rust
   conversion that reads a `usize` parameter as an index
   (`design/rust-sidecar-signatures.md`, section 4) becomes the general
   rule.
3. Stage 3, measured against the proofs that cast today.
4. Stage 2, with its scaling regressions.

Stage 1 should wait until the Rust sidecar work has landed, since both
change how a place's index is parsed and lowered.
