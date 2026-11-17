# First-class slices

This record describes the partially implemented slice-value design. Rust
specifications support slice values through the library's `Slice<T>` and
retain paired pointer/length parameters where the existing fold machinery
needs them. Current admitted positions and source restrictions are in the
[Rust reference](../docs/reference/rust.md#pure-functions-predicates-and-theorems).
The original proposal for a new built-in kernel slice type was not adopted.

## Representation by position (adopted)

A slice is one surface concept with two internal representations:

- **Pair:** data pointer and uint64 length for native and pure-function slice
  parameters, including existing folds and `unfold` equations.
- **Value:** `Slice<T>` from `library/rust/slice.click` for pure-function
  results, `Option` payloads, enum fields and library iterator contracts.

At their boundary, lowering constructs `Slice::Slice(p, n)` or projects a
value's pointer and length. One slice is one source argument, including
`old(bytes)` and `at(point, bytes)`; a caller with only a pointer and length
uses `slice::from_raw_parts(p, n)`. This keeps ordinary proofs independent of
the internal choice. A new position must work through lowering, printing and
expanded checking before the paired representation there can be removed.

The native importer still has paired locals and `slice_parts` paths. A
specification's slice-valued result is not evidence for general Rust functions
returning slices. The supported iterator `Option<&[u8]>` result has its own
library-value integration, described in [Rust iterators](rust-iterators.md).
Do not flatten a new general result into unrelated public pointer/length names.

## Operations and resources

`len()` and `as_ptr()` are the library projections. Methods, indexing and
subslices resolve from the receiver's inferred type, including `match` and
`let` binders, through [Typed method resolution](typed-method-resolution.md).
A constructed value's projections reduce to its fields without an unfold.

A subslice constructs a pointer offset and
`slice::subslice_len(a, b, s.len())`. The latter lowers through
`SpecExpression::Requires` and owes `a <= b <= s.len()` wherever Rust would
panic. A slice value is metadata, with no memory effect or new authority.
Indexing still needs both bounds and a covering held resource.

`views *s` and `owns *s` refer to the existing range through its data pointer.
Passing a subslice lends that subrange through the existing ledger; mutable
halves require disjoint ownership. A range based on a projection or a
function-result slice must match through checked pointer identity, rather
than manufacture access from a numeric address equality.

Slice-value equality is identity of data pointer and length. It is not Rust's
content-comparing `PartialEq`; content equality needs an explicit predicate
and read authority. Pointer identity retains its provenance, not just its
numeric address. A constructed slice does not itself establish a live Rust
reference or the `isize::MAX` byte-size bound. Native entry validity and actual
formation/access checks supply their independent obligations.

## Printing and cost

Name a subslice where it is constructed and its bounds are discharged.
`spec::required_constructions` retains that value so later goals can print the
same subslice without introducing new obligations. Other constructed values
print as the library constructor at their element type. Printed text must
lower back to the same term, including inferred binders and function results.

Projection and pair/value conversion do bounded work. Equality compares the
metadata, never enumerates elements, and resource operations use indexed
ranges. Changed positions need deterministic scaling controls and agreement
of ordinary, expanded and retained checking.

## Remaining decisions

General native slice locals/returns and removal of paired machinery remain
separate importer work. Broader mutable-slice values and non-scalar/nested
slice elements need precise validity, authority and interface rules before
admission. The built-in-product proposal and its initial migration sequence
are preserved in the [historical record](https://github.com/clicklang/click/blob/2175760b9/design/first-class-slices.md);
they are not instructions to replace the implemented library representation.
