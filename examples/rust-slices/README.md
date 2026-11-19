# Rust byte slices

This synthetic example verifies shared and mutable byte slices, `.len()`,
indexed reads and writes, local slice copies and reborrows, and a direct call
that passes a slice. Indexing proves the Rust `usize` bounds check before
forming an address. Byte mutation uses Click's existing ownership resources.

A Rust parameter `bytes: &[u8]` passes a shared byte pointer and a length.
Proofs write `bytes.len()` for the length. The pinned target's `usize` is a
64-bit unsigned value. Slice metadata is copied and passed together.

`read` and `write` have variable-length contracts. Their memory ranges keep
the 64-bit `bytes.len()` bound, so they state no limit on the length; lengths,
indices and bounds checks are all 64-bit.
`length` and `empty` inspect metadata without requiring a byte resource.
`increment_first` explicitly restates the resulting byte as
`to_integer(old(bytes[0]) + 1u8)` after execution. This checks that `solve`
relates the Rust increment's widened arithmetic to the sidecar's byte sum.

Build `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-slices/bytes.click
cargo run --bin click -- verify examples/rust-slices/bytes.click
```

Fixed arrays, subslices, slice returns, iterators, loops, indexed compound
assignment, and general `usize` arithmetic remain unsupported. This is
frontend evidence, not verification of an existing checksum library.
