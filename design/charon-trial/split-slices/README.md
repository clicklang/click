# Shared byte split_at checkpoint

`split.rs` and `split.click` are byte-identical copies of the original
`examples/rust-split-at` source and frozen sidecar. All four claims verify
through genuine, pinned Charon ULLBC: left/right lengths and left/right byte
reads. `empty.click` and `endpoints.click` check empty and endpoint results.
Integration tests also check full-width lengths, invalid midpoints, and empty
reads.

`copies.rs` retains a split tuple, copies it, replaces a tuple with another
split, and exercises source names that collide with component storage names.
Its three contracts verify without compiler-local observations.

The adapter recognizes the resolved shared byte `core::slice::split_at`
method and builtin two-element tuple. It stores each tuple field as a shared
pointer plus full-width usize length, preserving component order for copies
and ordinary field projections. Both results reuse the existing checked split
operation. General tuple construction/boundaries, borrowed tuples, mutable
splits, and non-byte splits remain unsupported.

To refresh and verify from the repository root, with the pinned tools active:

```sh
target/debug/click import lock design/charon-trial/split-slices/split.click
target/debug/click verify design/charon-trial/split-slices/split.click
target/debug/click import lock design/charon-trial/split-slices/copies.click
target/debug/click verify design/charon-trial/split-slices/copies.click
```

The empty/endpoint configs share the original split extraction; refresh their
lock identities together when refreshing that artifact. Ordinary tests check
frozen source/proof parity, boundaries, forged declarations/projections,
missing authority, false claims, tool agreement, expansion, and deterministic
work at extents 8/128/1024. The live gate re-extracts both sources and checks
transactional rejection of mutable/non-byte/tuple-return shapes.
