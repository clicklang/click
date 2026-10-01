# Rust byte slices

This synthetic example verifies shared and mutable byte slices, `.len()`,
indexed reads and writes, local slice copies and reborrows, and a direct call
that passes a slice. Indexing proves the Rust `usize` bounds check before
forming an address. Byte mutation uses Click's existing ownership resources.

A Rust parameter `bytes: &[u8]` lowers to `const uint8* bytes, uint64 bytes_len`;
`&mut [u8]` uses a mutable byte pointer. The pinned target's `usize` is a
64-bit unsigned value. The generated `<parameter>_len` name must not collide
with another parameter. Slice metadata is copied and passed together.

`read` and `write` have variable-length contracts. Their memory ranges use
`(int32)bytes_len`, so they require `bytes_len <= 2147483647u64`. This is the
current Click memory-range boundary; lengths and bounds checks are still
64-bit, and an index with a nonzero high word cannot alias a small byte range.
`length` and `empty` inspect metadata without requiring a byte resource.

Build `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-slices/bytes.click
cargo run --bin click -- verify examples/rust-slices/bytes.click
```

Fixed arrays, subslices, slice returns, iterators, loops, indexed compound
assignment, and general `usize` arithmetic remain unsupported. This is
frontend evidence, not verification of an existing checksum library.
