# Rust iterators: one generic model, per-type library contracts

Status: step 1 done, step 2 next. `library/rust/chunks_exact.click` declares
`ChunksExact<T>` with `len`, `nth`, `remainder` and `after_next` and the
axioms relating them, and a proof reads a value with those methods. A Rust
unit with `"iterators": "library"` imports its `chunks_exact` iterators as
values of that type, and construction, `remainder()` and loops, including
one that reads through each chunk, are proved from the contract
(`examples/rust-chunks-exact/chunks.click`). The loop fact is a library
function, `after(it, k)`, the iterator after `k` calls of `next()`: a loop
carries `iter == start.after(iterations)`. The unit option is
temporary and is removed with the old model (migration step 4). The loop's starting iterator is spelled with the
existing snapshot form, `at(loop(i).entry, iter)` (open question 2).

## Problem

Click currently models each supported Rust iterator kind by hand. Each kind
costs work in two places.

- **Importer lowering.** `src/languages/rust/lowering/` has `shared_arrays.rs`
  for `slice::Iter`, `enumerate.rs`, `ranges.rs` for `a..b` and `a..=b`, and
  `chunks.rs` for `ChunksExact`, about 830 lines in all. Each file turns one
  iterator type into hidden C locals and hand-written `next` code: a slice
  iterator's `_base`, `_length` and `_remaining`, or a chunk iterator's
  `_cursor`, `_remaining`, `_size` and `_tail`.
- **Accessor views.** `surface.rs` (`rust_iterator_method`,
  `rust_iterator_accessors`) maps each kind's Rust methods onto those hidden
  locals. For example, `iter.len()` on a slice iterator reads `_remaining`,
  and `iter.as_slice()` reads `_base + (_length - _remaining)`.

Proofs that go past the accessors have to reason about the hidden locals.
The adler2 proofs mention them about 2,700 times
(`__rust_mir_62_remaining` and others). Adding an iterator type means
another lowering file, another accessor table and another set of hidden
names. That cannot scale to the hundreds of stdlib types (and other
libraries' types) Click will eventually need.

## Principle

Iterators are a core part of Rust, so Click supports iterators **generically**.
Click does not special-case any particular iterator **type**. A type such as
`ChunksExact`, `slice::Iter`, `Enumerate` or `Range` is described by
contracts in the Click library, the same way `library/rust/vec.click`
describes `Vec<T>`. Those contracts are trusted: they are assumptions, like
an `extern fn` contract. A later effort could verify the real implementations
against them. That is not part of this proposal.

## Generic iterator model (in Click)

- **An iterator value stands for the finite sequence of items it will still
  yield.** Click knows two things about any iterator value `it`:
  - `it.len()`: how many items are left. This is Rust's
    `ExactSizeIterator::len` where Rust has it.
  - `it.nth(k)`: the item the `k`-th following `next()` would return, for
    `k < it.len()`. It is a pure observation, not Rust's consuming
    `Iterator::nth`.
- **One law covers every `next()`.** When `it.len() > 0`, `next()` returns
  `Some(it.nth(0))`. Afterwards the iterator has `len() == old.len() - 1`
  and `nth(k) == old.nth(k + 1)`. When `it.len() == 0`, `next()` returns
  `None` and leaves the iterator unchanged.
- **The loop fact.** A `for x in it` loop provides `iterations` already. Let
  `start` be the iterator's value at loop entry. On pass `k`, where `k` is
  `iterations`:
  - the loop variable `x` is `start.nth(k)`;
  - `iter.len() == start.len() - k`.

  These facts follow from the `next` law by induction. No iterator type
  appears in them.

  As built, the loop fact is not a verifier rule. Each type's library file
  declares `after(it, k)`, `it` after `k` calls of `next()`, with the
  axioms `after(it, 0) == it`, `after_next(after(it, k)) == after(it, k +
  1)`, `len(after(it, k)) == len(it) - k` and `nth(after(it, k), j) ==
  nth(it, k + j)`. A loop states `iter == start.after(iterations)` as an
  ordinary invariant; the second axiom preserves it across a pass and the
  last gives the loop variable. The cost is one function and four axioms a
  type; the gain is that nothing in Click knows about iterator loops.

Nothing in this model knows what any particular iterator yields. That is
what the library contracts are for.

## Per-type contracts (in the library)

Each iterator type gets a short library file. It states only what the
constructor produces and the type's own extra methods. For example:

- `bytes.chunks_exact(n)`:
  - requires `n != 0`;
  - `len() == bytes.len() / n`;
  - `nth(k)` is the slice of length `n` starting at `bytes + k * n`;
  - `remainder()` is the last `bytes.len() % n` bytes. It is fixed: `next`
    leaves it unchanged.
- `bytes.iter()`: `len() == bytes.len()`, and `nth(k)` is `&bytes[k]`.
  `as_slice()` is the `len()` bytes ending at `bytes + bytes.len()`.
- `it.enumerate()`: `len()` is the inner iterator's `len()`, and `nth(k)` is
  `(k, inner.nth(k))`.
- `a..b`: `len()` is `b - a` when `a <= b` and zero otherwise, and `nth(k)` is
  `a + k`. `start` and `end` are the fields. `a..=b` is similar, with
  `start()`, `end()` and `is_empty()`.

Each of these is a set of `axiom`s or `extern fn` contracts over the
generic functions. None of them needs verifier code.

## What a proof looks like

`examples/rust-chunks-exact`:

```rust
let chunks = bytes.chunks_exact(4);
let tail = chunks.remainder();
for chunk in chunks { let first = chunk[0]; let last = chunk[3]; }
tail.len()
```

The proof combines the loop fact with the `chunks_exact` contract. On pass
`k`, `chunk` is `start.nth(k)`, which is `bytes + 4 * k` with length 4.
`iter.len() == bytes.len() / 4 - k` holds as well. The read bound
`4 * k + 4 <= bytes.len()` follows from `iter.len() > 0`, plus the
`integer::` quotient lemmas, cited explicitly. There is no cursor, no
remaining-byte count and no hidden name. The loop needs no invariant about
the iterator, only `decreases iter.len()`.

## Where the hidden state goes

The importer still has to run the loop. Instead of one hand-built C model
per kind, an iterator value becomes a value of a library type, as a `Vec<T>`
is today. Each `next` call becomes a call whose contract is the generic
`next` law. Each constructor becomes a call whose contract is that type's
library contract. The lowering files above are replaced by this one path.
The per-kind accessor table, `RustIteratorKind` and the old spellings
(`iter_remaining`, `<prefix>_cursor`, `__rust_mir_*_remaining`) are removed.

## Open questions

1. **Pointer- and slice-valued items.** A `Vec<T>` holds integers. An
   iterator's items can be references or slices, which are a pointer plus a
   length, inside an `Option`. Library spec functions that return pointers
   already exist (`examples/rbtree` returns `struct rb_node*`). Carrying
   `Option<&[u8]>` through the importer as a library value is unproven, and
   may need kernel support. Settled: none is needed. The importer keeps the
   `Option` as its tag, pointer and length, read from `it.nth(0)`. The
   pointer is the function result `slice::as_ptr(it.nth(0))`, equal to
   `bytes + k * n` by a cited axiom, and a read through it is placed in the
   slice's view from that equality and the offset's bound as a machine
   value.
2. **Naming `start`.** The loop fact needs the iterator's value at loop
   entry. Candidates:
   - `loop(i).start`, a new built-in like `iterations`;
   - the program's own local that the loop consumes, such as `chunks` in
     `for chunk in chunks`, read at loop entry;
   - an existing snapshot form.
3. **Iterators advanced before the loop or resumed after a `break`.** In
   those cases `iterations` is not the number of items consumed. The loop
   fact is stated relative to the value at loop entry, so it still holds.
   A proof that relates it to construction must account for the earlier
   `next` calls.
4. **Quantified contracts.** `nth(k)` facts are `forall k`. Proofs
   instantiate them at `k = iterations`, explicitly for now. A future
   `solve` search for a single applicable library theorem (pending Vec work,
   task "Vec 2") would remove those citations. Simple checking must stay
   linear in the proof, so contracts must not be instantiated eagerly.
5. **Relation to a future "library interface" or "module interface".**
   Each per-type file is an interface: types, functions and contracts that
   are trusted now and verifiable later. If Click grows such a concept, these
   files should become its first instances.

## Migration

1. Done: the generic model plus the `ChunksExact` contract on
   `examples/rust-chunks-exact`, which settled open questions 1 and 2.
2. The other `chunks_exact` fixtures, then adler2.
3. Slice iterators, `enumerate` and ranges onto their library contracts.
   This includes inclusive ranges, currently blocked by
   `bugs/solve-exhausts-its-budget-spelling-premises-of-an-inclusive-range-loop.md`,
   which should be re-checked under the new model.
4. Remove the per-kind lowering, the accessor table and the old spellings,
   and with them the `"iterators": "library"` unit option, which exists only
   so fixtures can move one at a time.
