# Shared Rust exact chunks and remainder

`chunks.rs` keeps the ordinary stored `ChunksExact` iterator and saves its
remainder before consuming it, as adler2 does. Its loop reads the first and
last byte of each four-byte shared chunk. The sidecar checks each read,
termination, and the fixed remainder's length, for arbitrary input bytes of
any length a slice can have. Every input byte equals its value at function
entry.

The iterator (`docs/reference/rust.md`, Exact chunk iterators and remainder)
is held as its own fields, as `core::slice::ChunksExact` declares them: `v`,
the chunks still to come, `rem`, the remainder, and `chunk_size`. The
importer runs `core`'s own `chunks_exact`, `next` and `remainder` over them,
so the proof cites no chunk contract and names no generated local.

- Where the loop's iterator stands: `v` is the bytes from offset
  `bytes.len() - bytes.len() % 4 - iter.v.len()` on,
  `iter.v == bytes + (bytes.len() - bytes.len() % 4u64 - iter.v.len())`,
  with `iter.chunk_size == 4u64`. `decreases iter.v.len()` ranks the loop.
- A pass's `next()` yields `v`'s first four bytes as `chunk` and moves `v`
  on by four. The `maintain` script splits on `4u64 <= iter.v.len()`, the
  test `next` makes.
- Moving `v` on owes its offset's bound in the forms the step reads,
  `to_integer(k) + 4 <= to_integer(bytes.len())` and
  `to_integer(k + 4u64) <= to_integer(bytes.len())`, and the invariant is
  carried by regrouping `(bytes + k) + 4u64` as `bytes + (k + 4u64)` from
  `to_integer(k) + 4 <= 18446744073709551615`.
- The remainder `tail` is `rem`, the last `bytes.len() % 4` bytes, set when
  the iterator is built.

The same proof verifies `for chunk in &mut chunks` followed by a later
`chunks.remainder()` (`design/charon-trial/borrowed-chunks`): it names the
loop's iterator as `iter`, whichever local holds it. Neither construction nor iteration copies bytes or grants
write permission; the compiler rejects writes through a chunk or remainder.
Zero sizes require an unreachable-panic proof. Mutable chunks, iterator
copies and adapters are outside this example.

Run `click verify examples/rust-chunks-exact/chunks.click`.
