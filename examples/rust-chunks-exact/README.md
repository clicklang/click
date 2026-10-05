# Shared Rust exact chunks and remainder

`chunks.rs` keeps the ordinary stored `ChunksExact` iterator and saves its
remainder before consuming it, as adler2 does. Its loop reads the first and
last byte of each four-byte shared chunk. The sidecar checks each read,
termination, the cursor's partition of the original byte range, and the
fixed remainder's length. Input bytes are arbitrary, with length `0..=1000`.
At loop exit the cursor equals the tail pointer; together with the complete
range and tail lengths, this proves the input partition has no gaps. Every
input byte equals its value at function entry.

The iterator stores a cursor, remaining complete-byte length, chunk size,
and fixed tail pointer and length. It has no generated processed-count local.
Yielding a chunk advances the cursor and reduces the remaining complete
range before executing the source body. Chunk slices use the original byte
views; neither construction nor iteration copies bytes or grants write
permission. The compiler rejects writes through a chunk or remainder.

Stored iterators support consumption by value or `for chunk in &mut chunks`;
the borrowed form permits later `remainder()` calls. Direct and nested
`for chunk in bytes.chunks_exact(size)` loops use the same state. The tail
remains available after iteration when saved beforehand or when the iterator
was borrowed. The current memory model requires the input length to fit in
`i32::MAX`. Chunk sizes retain all 64 bits, including sizes larger than the
input. Zero sizes require an unreachable-panic proof, including on empty
input. Mutable chunks, iterator copies/adapters, and explicit `next()` calls
are outside this increment. The pinned checksum libraries remain unverified.

The proof uses source read and assignment frontiers, named snapshots, and
`execute_until(back_edge())` to observe checked iterator progress. Invariant and
ranking closure check the input partition and termination separately.

```sh
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/rust-chunks-exact/chunks.click
cargo run --bin click -- verify examples/rust-chunks-exact/chunks.click
cargo run --bin click -- audit examples/rust-chunks-exact/chunks.click
```
