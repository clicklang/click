# An index keeps its type until it is an offset

This record preserves the typed-index decisions implemented in October 2026.
The staged migration is complete; heap-block extents followed in
[Heap extents](heap-extents.md). Current public behavior is specified in the
[C reference](../docs/reference/language/c.md) and
[Rust reference](../docs/reference/rust.md).

## Index and range rules

An index keeps its integer type until it becomes an offset. A C `int` index
is sign-extended; a C `size_t` or Rust `usize` index retains its 64-bit value.
The kernel does not silently narrow a wide index because facts show it fits.
A written narrowing cast still means truncation and can name a different
address from the original program's access.

`CMemoryRange` distinguishes `Int32` and `UInt64` coordinates. Any 64-bit
bound selects the wide kind, including a constant or nonzero start. Signed
64-bit bounds are read through sign extension; range guards exclude negative
values. A range's kind must not depend on facts established by its contract.

Wide membership requires the selected index to lie between the range's bounds
and the complete byte extent to fit the modeled object limit,
`end <= i64::MAX / element_width`. Wide scaled offsets are exact products;
constant folding must not turn them into wrapping offsets. Calls must prove
range guards, including `start <= end`, before transferring a range.
Entry may assume guards already established by its caller.

Wide ownership can split into windows and suffixes and rejoin after calls.
Cross-kind reasoning must compare exact byte offsets, rather than interpret
one kind's bounds through the other's comparisons. Full-width `viewable`,
quantifiers, folds and order reasoning support the same coordinates.
The checksum proofs use a full-width specification with a bounded int32
per-batch layer; the old overall `INT_MAX` length cap is unnecessary.

## Representation and scaling

Keep range-kind identity in equality, hashing and ordering. Narrow-only
accessors must refuse wide ranges. A low-word fact cannot determine an entire
64-bit bound. Constant readers, struct strides and cross-width footprints must
respect the same distinction.

Queries use the selected base and index, without scanning unrelated ranges or
all inequalities sharing a bound. Existing deterministic regressions live in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`,
`src/scaling_tests/kernel/tests/resource_scaling_tests.rs` and
`src/scaling_tests/surface/tests/scaling_tests.rs`.

## Rulings

The October 16 rejection of format-carrying machine nodes and a common
comparison family was superseded by the accepted
[machine-integer design](machine-integers.md). It must not guide new work.
Variable width still comes from its context; the debug width audit rejects
inconsistent uses. The current representation is described in
[Kernel](../docs/internals/kernel.md).

The [original migration record](https://github.com/clicklang/click/blob/2175760b9/design/typed-indices.md)
contains the staged experiments and historical site counts. The
[retired Rust-signature proposal](https://github.com/clicklang/click/blob/2175760b9/design/rust-sidecar-signatures.md)
is historical too: Rust signatures, reference fields and full-width slice
indices are implemented, as the current reference records.
