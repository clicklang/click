# First-class slices

Status: proposal. Nothing here is implemented yet.

## Problem

A Rust slice, `&[T]` or `&mut [T]`, is a fundamental Rust value: a data
pointer and a length that travel together. In Click it exists only as a
parameter, and is split into two names.

- **`fn` and pure-`function` parameters.** `bytes: &[u8]` becomes a pointer
  `bytes` plus a synthesized `bytes_len: uint64`. The parser rewrites
  `bytes.len()` to `bytes_len` (`take_rust_slice_len`). A pure-function call
  spreads one slice argument into two arguments (`spread_slice_arguments`).
  A caller with no slice in scope writes `size(p, n)`.
- **Everything else refuses a slice.** That covers a pure function's result,
  a `fn` result, an `Option` or `Result` payload, a spec enum field, a
  theorem or predicate binder, and a library `type`'s functions. The refusal
  tells the user to pass "a slice as its pointer and a `usize` length".
- **The importer keeps every slice as two C locals.** Parameters, `split_at`
  halves, chunk items (`{o}_pointer`, `{o}_len`) and chunk remainders
  (`{it}_tail`, `{it}_tail_len`) all work this way. `slice_parts` resolves
  each one back to its pair. `Option<&[u8]>` is flattened by hand into three
  locals. Slice-returning functions are unsupported
  (`docs/reference/rust.md`, "General slice returns").

The generic iterator model (`design/rust-iterators.md`, open question 1) is
where this hurts most. Item `k` of `bytes.chunks_exact(n)` is a slice, and
`next` returns `Option<&[u8]>`. Neither can be stated today, except by
splitting each item into two library functions.

## Principle

Fundamental features of a supported language are supported directly in
Click. A slice becomes a value type of the spec language. It can appear
anywhere an integer or a pointer can, with Rust's own operations. It is not
a library type, because the language itself has slices.

## The type

`&[T]` and `&mut [T]`, for a scalar `T` at first, are spec value types in a
Rust sidecar. They are accepted as:

- `fn` and pure-`function` parameters and results;
- `ensures result` of a `fn` or `extern fn`;
- binders of theorems, predicates, `forall`, `exists` and `let`;
- fields of a spec enum, and type arguments such as `Option<&[u8]>`;
- parameters and results of a library `type`'s functions.

The element type stays scalar for now, matching today's slice parameters.
Slices of records or of slices come later.

### Operations

The names are Rust's.

| Spelling | Meaning |
|---|---|
| `s.len()` | its length, a `usize` |
| `s.as_ptr()` | its data pointer, `*const T` (`as_mut_ptr()` for `&mut`) |
| `s[i]` | element `i`, a memory read: needs `views`/`owns` of it, and `i < s.len()` |
| `s[a..b]`, `s[a..]`, `s[..b]` | the subslice, a slice value; `a <= b <= s.len()` is required |
| `*s` | the whole referent, as a resource: `views *s` is `views s[0..s.len()]` |
| `slice::from_raw_parts(p, n)` | the slice with data `p` and length `n`, for a caller holding a pointer and a length |
| `s == t` | identity: the same data pointer and the same length (see Equality) |

A subslice is a value with no memory effect. `bytes[4..8]` is just the slice
with data `bytes.as_ptr() + 4` and length 4. Reading through it needs the
same `views` as reading `bytes[4]` to `bytes[7]`.

`s.as_ptr()` and `slice::from_raw_parts` are rare in proofs. They exist so
that every slice fact can be spelled, including one the verifier prints
about a slice with no source name.

### Equality

`s == t` on slice values means identity: the same data pointer and the same
length, as `==` on pointers means the same address. This departs from Rust,
whose `PartialEq` on slices compares contents, and the reference documents
it. Specs almost always mean identity (this chunk *is* `bytes[4k..4k+4]`).
Contents are compared explicitly, with `bytes::equal` or a library
contents predicate, which needs `views` of both slices.

## Kernel representation

A slice value is a built-in product of two values that already exist: a
pointer value, `CValue::Pointer` with its provenance and extent, and a
`uint64` length. Concretely:

- a new value type (for example `AlgebraicValueType::Slice { element,
  mutable }`) and value (for example `AlgebraicValue::Slice { data, len }`);
- two projections, `data` and `len`. A projection of a constructed slice
  reduces at once, `len(slice(p, n)) == n`, as a constructor field
  projection does today;
- equality is componentwise: equal data and equal length.

Nothing about memory changes. Reads, `views` and pointer formation still go
through the data pointer and the existing `CMemoryRange` resources. A slice
only keeps the pair together and gives it a type.

This must stay cheap. Projection is constant time, no slice is compared
structurally on a hot path, and the checker never enumerates a slice's
elements. Any representation change follows
`docs/internals/verification-efficiency.md` and adds a scaling regression.

## Resources: `views` and `owns`

A slice resource is the existing range resource over its data pointer. Read
authority, borrow tracking and loan bookkeeping are all unchanged.

- `views *s` is `views s.as_ptr()[0..s.len()]`, and `owns *s` is the same
  with ownership. `views s[a..b]` is the range `a..b` of that.
- Reading `s[i]` is a read at `s.as_ptr() + i`. It needs a range covering it
  and `i < s.len()`, exactly as reading `bytes[i]` does today.
- A subslice does not create a resource. Reading `bytes[4..8][1]` reads
  `bytes + 5` under the caller's `views *bytes`, as reading `bytes[5]`
  does.
- Passing a subslice to a callee that `views *s` lends the range `a..b` of
  the caller's resource. This is the same sub-range lending that borrowed
  byte ranges use today (`examples/borrowed-slice`). Mutable halves from a
  split lend disjoint `owns` ranges.

Two points need tests in step 1, because the existing machinery has only
ever met them as pointer arithmetic on a named parameter:

- **Slices whose data comes from a function result.** A slice whose data is
  the result of a library or `extern` function, such as an iterator item, is
  covered by the caller's range only through an equality such as
  `chunk == bytes[4k..4k+4]`. Memory resolution has to use that equality to
  match the read at `chunk.as_ptr() + 3` against `views *bytes`. The kernel
  reasons with pointer equalities, but no current example reads memory
  through a pointer that is known only by equality to a function result, so
  this is unproven.
- **Ranges based on a projection.** A resource whose base is `s.as_ptr()`,
  for a slice `s` bound by `let` or `forall`, has to be reduced to the
  constructed pointer before resources are matched. Otherwise two spellings
  of one range fail to match.

## Compatibility

Existing proofs keep working unchanged.

- **The spellings stay the same.** A slice parameter `bytes` becomes one
  slice-valued parameter. `bytes.len()`, `bytes[k]`, `*bytes` and
  `views bytes[0..bytes.len()]` keep their meaning. What changes is
  underneath: `bytes.len()` is now a projection, not a renamed `bytes_len`.
- **The hidden name `bytes_len` stops being nameable.** Proofs that wrote it
  directly are migrated first, or for one release it is accepted as an alias
  that prints `bytes.len()`.
- **Pure-function calls take a slice argument.** `prefix(bytes, i)` already
  reads that way. Calls that pass a pointer and a length, `size(p, n)`,
  become `size(slice::from_raw_parts(p, n))`. Printed proofs print the slice.
- **Contract entry is unchanged.** The incoming pointer and length are
  packaged as one slice value. The entry extent fact
  (`c_function_contract_entry`, `slice_length_parameter`) is still derived
  from the two parts.
- **C sidecars are not affected.** The kernel type is language-neutral, so a
  C or C++ surface could later adopt it (for a `T* p, size_t n` pair), but
  that is not part of this proposal.

## Representation by position (adopted)

Status: adopted after a probe. Reading a slice through a `match` on
`Slice<T>` works in a plain pure function, but not yet inside a range fold,
under a cast, or in `peel`'s defining equations. So one representation
everywhere would mean fixing all of those before today's proofs keep
working.

A slice is therefore one concept at the surface with two internal
representations, chosen by position:

- **Pair:** the data pointer and the length, as today. It is used where the
  machinery already works on pairs: `fn` slice parameters and pure-function
  slice parameters, including folds and `peel`.
- **Value:** a `Slice<T>` from `library/rust/slice.click`. It is used where a
  pair cannot go: results, `Option` payloads, enum fields, and library
  contracts such as iterator items.

Where the two meet, the lowering converts mechanically. A pair becomes the
value `Slice::Slice(p, n)`, and a value becomes the pair of its two field
projections. Proof text never depends on the choice: a slice is always one
argument and one name, printed in Rust spellings. Migration flips a position
from pair to value one PR at a time, fixing that position's gaps, until the
pair representation can be deleted.

In place: slice parameters (pair), one slice argument per call, and slice
values as pure-function results, `Option` payloads and enum fields. A value
is read with `.len()` and `[i]` through an inline projection `match` that
reduces on a constructed slice. `.as_ptr()` and a value passed to a slice
parameter go through `slice::as_ptr`, because a pointer-valued `match` does
not lower as a value yet. Still open: slices bound by `match` arms or `let`,
subslices `s[a..b]`, and the importer's slice locals and returns.

## Importer

There are two stages.

1. **Specs first.** Slices become first class in specs, while the importer's
   C model still holds each slice as a pointer local plus a length local.
   Wherever the model meets a spec (a contract, a call, an `extern fn`
   result), the importer packages the pair into a slice value or unpacks it.
   This alone permits:
   - slice-valued pure functions;
   - library functions that return slices, such as `ChunksExact` item `k`
     and `remainder()`;
   - `Option<&[u8]>` in contracts.
2. **Slice values in the model.** A slice local becomes one value instead of
   two locals. This adds:
   - slice-returning Rust functions;
   - `Option<&[u8]>` locals (`next`'s result);
   - `split_at`'s pair.

   `slice_parts`, the chunk option's flattened fields and the `_len` naming
   convention all go away.

The iterator migration needs stage 1 for its contracts. It needs stage 2 for
`next` to return `Option<&[u8]>` without hand flattening.

## What a proof looks like

The `chunks_exact` contract from `design/rust-iterators.md` becomes
directly expressible:

```click
// item k of bytes.chunks_exact(n), for k < bytes.len() / n
ensures result.nth(k) == bytes[k * n .. k * n + n];
ensures result.remainder() == bytes[bytes.len() - bytes.len() % n ..];
```

In the loop, `chunk == bytes[4 * iterations .. 4 * iterations + 4]` is one
slice equality. `chunk[3]` is in bounds because `chunk.len() == 4`, and it
reads `bytes[4 * iterations + 3]` under the function's `views *bytes`.

## Open questions

1. **Mutable slices.** Are `&mut [T]` and `&[T]` one value type with a flag,
   or two types? Is a mutable slice's identity plus `owns *s` enough, with
   writes going through the existing memory model?
2. **Length bound.** A Rust slice of `T` is at most `isize::MAX` bytes.
   Should every slice value carry that as a fact? Contract entry assumes it
   for parameters today.
3. **Printing a slice with no source name.** Candidates are
   `bytes[a..b]`, when its data is a known offset into a named slice, and
   `slice::from_raw_parts(p, n)` otherwise. This is needed for spellability.
4. **Non-scalar elements** (records, slices of slices). These are deferred
   until a program needs them.

## Migration

1. Kernel slice value type, its projections and equality, with unit tests
   and a scaling regression, plus the two resource tests above.
2. Rust sidecar surface: the type in every position listed above, the
   operations, and parameters re-expressed as single slice values. Existing
   proofs and `docs/reference/rust.md` keep their spellings, and the docs
   gain the new positions.
3. Importer stage 1: package and unpack at spec boundaries, slice-valued
   library functions and `extern fn` results.
4. Iterator model step 1 (`design/rust-iterators.md`) on `chunks_exact`,
   using slice items.
5. Importer stage 2: slice locals, slice returns and `Option<&[u8]>`, then
   remove the paired-local machinery.
