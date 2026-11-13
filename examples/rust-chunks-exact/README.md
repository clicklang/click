# Shared Rust exact chunks and remainder

`chunks.rs` keeps the ordinary stored `ChunksExact` iterator and saves its
remainder before consuming it, as adler2 does. Its loop reads the first and
last byte of each four-byte shared chunk. The sidecar checks each read,
termination, and the fixed remainder's length, for arbitrary input bytes of
any length a slice can have. Every input byte equals its value at function
entry.

The iterator (`docs/reference/rust.md`, Exact chunk iterators and remainder)
is one value of the library's
`ChunksExact<uint8>` and the proof cites the contract in
`click::rust::chunks_exact`. The unit sets `"iterators": "library"`, so the
iterator is imported through Rust's own interface: each pass calls
`ChunksExact::next(&mut iter)`, which returns `Option<&[u8]>`, and
`chunks.remainder()` is a call to `ChunksExact::remainder`. No cursor,
remaining-byte count or generated local is named. The `preserve` script
splits on `0u64 < iter.len()` before the `next()` call.

- What `chunks_exact` builds: `len_chunks_exact`, `nth_chunks_exact` and
  `remainder_chunks_exact`, applied to `Slice<u8>::Slice(bytes, bytes.len())`.
- Where the loop's iterator stands: one invariant,
  `iter == chunks_exact::after(start, iterations)`, the starting iterator
  after that many `next()` calls, beside the count
  `to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64)`.
- The chunk a pass binds: `nth_after` gives it as chunk
  `bytes.len() / 4 - iter.len()` of the start, and `nth_chunks_exact` places
  that at `bytes + k * 4` with length 4.
- Each read owes its offset's bound as the machine value the program
  computes, `to_integer(k * 4u64 + 3u64) < to_integer(bytes.len())`.
- `after_next_after` carries the invariant across the pass's `next()`.

The loop is imported as a `while (1)` whose header reads `iter.len()` and
leaves by `break` when it is zero, so the `preserve` script splits on
`0u64 < iter.len()` with a proof `if`; the empty arm takes the `break` with
one `step()`.

The same proof verifies `for chunk in &mut chunks` followed by a later
`chunks.remainder()`: it names the loop's iterator as `iter`, whichever
local holds it. Neither construction nor iteration copies bytes or grants
write permission; the compiler rejects writes through a chunk or remainder.
Zero sizes require an unreachable-panic proof. Mutable chunks, iterator
copies and adapters are outside this example.

Run `click verify examples/rust-chunks-exact/chunks.click`.
