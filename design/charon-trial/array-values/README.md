# Whole-array assignments through local references

`arrays.rs` and `arrays.click` preserve the existing `rust-array-values`
source and sidecar byte for byte. Previously, ULLBC's whole-array reference
assignment fell into scalar lowering and emitted a misleading by-value
parameter/return diagnostic, although the fixture has neither. The adapter now
lowers these assignments to the existing checked compact array-region operation.
The fixture imports successfully; its full sidecar deliberately records a
proof gap at `copy_reference`: the kernel currently requires a represented
local source for compact copying. External destination regions are likewise
outside this compact operation. No unsupported claim is counted as verified.

`bounds.rs` is synthetic positive coverage of the supported local-storage
boundary. Mutable references into automatic scalar arrays support captured
literal replacement, repeated fills, snapshot copying, self-copy, and empty
arrays. A swapped literal reads both old elements before writing either; an
independent copy keeps its bytes after source mutation. `i32`, `u8`, and `u32`
are covered. Fill and copy tests at 8, 1024, and million elements assert compact
storage, equal lowered statement count, an actual checked reference-region
write, and bounded deterministic proof work.

The shared checker verifies ten positive contracts and rejects false results.
`verify`, `profile`, `audit`, and expanded certificates agree. Live tests
re-extract the positive checkpoint, reject writes through shared references
and conflicting mutable borrows, and retain rejection of genuine by-value
array parameters and aggregate returns. The parity sweep re-extracts the
unchanged full fixture and requires its precise expected proof-gap diagnostic.

`local-scalar-array-reference-assignment-v1` changes the semantic profile and
checkpoint identities. Compiler pins, extraction flags, and previous ULLBC
bytes remain unchanged. External Charon locks require explicit refresh.

```sh
scripts/check.sh --charon-live
cargo nextest run --lib --test rust_import -E 'test(charon_array_reference_) | test(charon_array_values_)'
```

The migration inventory remains 9/16 fully verified: four normalization gaps
and three proof gaps. Next extend compact array snapshots and writes to
arbitrary borrowed storage with checked read/write authority, initialization,
alignment, preserved bytes and neighboring storage, and bounded work. Reuse
the frozen source as the regression; do not materialize one operation per
array element or rewrite the source to use local-only storage.
