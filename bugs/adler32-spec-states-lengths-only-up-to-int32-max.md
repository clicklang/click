# The shared Adler-32 specification states lengths only up to `INT32_MAX`

Priority: P2.

Soundness: incomplete. The C/Rust correspondence still proves its result
only for inputs of at most 2,147,483,647 bytes (the zlib and adler2 trials
now cover every length).
Nothing false is accepted: every contract that uses the specification writes
its narrowing explicitly (`((bytes.len() as u32) as i32)` in Rust,
`(int32)len` in C), and states the matching `requires` bound.

## Current state and violated invariant

`design/adler32/project/adler32-spec.click` defines `adler_byte_sum`, `adler_weighted_sum`,
`adler_spec_a`, `adler_spec_b` and `adler_spec_checksum` over an `int32`
length. The kernel has not needed that since typed-indices stage 3 (see
`design/typed-indices.md`): a 64-bit count bounds a range and indexes memory
directly. The specification and the proofs built on it still carry the old
limit:

- the adler2 Rust trial (`design/adler32/project/adler2/`): 25 `requires
  ... <= 2147483647u64` preconditions, the bound library
  `bounded-count.click`, which reads each `usize` count through
  `((count as u32) as i32)`, and about 1,900 `int32` uses in 19 files;
- the zlib C trial (`design/adler32/project/zlib/`): 8 files cite the signed
  limit, and its README states termination "through the shared signed length
  limit";
- the C/Rust correspondence (`design/adler32/project/checksum-correspondence.md`,
  `adler2/correspondence.click`), which equates both trials with the same
  specification, so neither side can be widened alone.

The invariant: the checksum claims cover every length the original `usize`
or `z_size_t` argument can hold, as the original programs do.

## Reproduction

The specification cannot be applied to a `uint64` length. A machine scalar
argument takes its declared parameter type, with the native conversion
(`docs/concepts/pure-functions.md`), so a 64-bit length is narrowed. This
theorem, appended to a copy of `design/adler32/project/adler32-spec.click`, verifies:

```click
theorem probe(bytes: uint8[], length: uint64) {
 requires length == 4294967296u64;
 ensures adler_byte_sum(bytes, length) == 0 by {
  have (int32)length == 0 by simp();
  rewrite((int32)length == 0);
  apply(adler_sum_empty(bytes, 0));
  simp();
 }
}
```

Read as an Adler-32 statement this is false: it says that the first 2^32 bytes
of every array sum to zero. Under the documented conversion it is true,
because the length wraps to 0. It shows that the specification cannot be
widened by changing callers alone: its parameter types must change.

## Migration prerequisites

The selected API is `uint64` lengths and `Integer` checksum sums. Weighted-sum
coefficients also need mathematical `Integer` arithmetic so that subtracting
weights does not wrap. Scalar induction now supports a full-width `uint64`
measure; its range-fold regression is
`mdtests/uint64_measure_induction_counts_a_range_fold.md`.

Widening the shared specification needs `adler_byte_offset_association` over
`uint64` offsets. `normalize() using` now equates `(bytes + prefix) + suffix`
with `bytes + total` from the cited exact sum `to_integer(total) ==
to_integer(prefix) + to_integer(suffix)`
(`mdtests/normalize_using_adds_element_indices_by_a_cited_integer_sum.md`); a
native wrapping sum alone still does not justify the address equality.

## Progress

The migration runs in stages, each keeping every trial verifying.

1. Done: `design/adler32/project/adler32-spec-u64.click` states every
   definition and theorem of the shared specification over `uint64` lengths
   and `Integer` sums and weights, with the suffix `_u64`; each signed length
   bound is replaced by the unsigned no-overflow condition.
   `adler32-spec-bridge.click` proves the two specifications equal at every
   pair of lengths with one exact value (`adler_spec_checksum_bridge` and its
   parts). The nightly test
   `adler_uint64_specification_agrees_with_the_int32_one_and_does_not_narrow`
   verifies both, a sum past 2^32, and that the wrap probe above no longer
   goes through over `uint64`.
2. Move the zlib proofs to the `uint64` specification.
   a. Done: every zlib C contract states its result with
      `adler_spec_checksum_u64(old(buf), old(len), ...)`. Each proof applies
      `adler_spec_checksum_bridge` at entry, except the two-call client,
      which composes its callees with `adler_spec_checksum_concat_u64`. The
      `len <= 2147483647u64` requirements remain.
   b. Done: the full-stream and canonical proofs carry their running prefix
      over `uint64` (each NMAX batch and short path keeps its int32 proof and
      joins through the bridge), so `full-stream.click`, `canonical.click`
      and `incremental.click` no longer require `len <= 2147483647u64`; the
      zlib trial covers every length its view admits. The int32 helpers in
      `full-stream-helpers.click` and `canonical-helpers.click` that only the
      old outer loops used are still present, for the final stage to delete.
3. Move the adler2 proofs to the `uint64` specification.
   a. Done: the public `adler2::adler32_slice` and `Adler32::write_slice`
      contracts (`public-general.click` and the constant-length
      `public-*.click` files) and the incremental and resumed clients state
      their results with `adler_spec_checksum_u64(data, data.len(), 1, 0)`
      and `adler_spec_a_u64`/`adler_spec_b_u64` at `bytes.len()` (or the
      constant `uint64` length). Each `write_slice` applies
      `adler_spec_a_bridge`/`adler_spec_b_bridge` to the computation's int32
      result, using `adler_bounded_count` for the narrowed length; the two
      clients compose their calls with `adler_spec_a_concat_u64`,
      `adler_spec_b_concat_u64` and `adler_spec_extensional_u64`. The
      `Adler32::compute` contracts, the correspondence, the
      `len <= 2147483647u64` requirements and the int32-indexed
      byte-preservation clauses remain.
   b. Done (3b-i): `Adler32::compute` (`general-compute.click`) states
      `adler_spec_a_u64`/`adler_spec_b_u64` at `bytes.len()` and has no
      length requirement. Every loop (full batches, aligned remainder,
      scalar tail) carries both lane residues over `uint64` at its actual
      iterator cursor; batch-local counts (at most 22208) stay `int32`. Four
      new `_u64` step lemmas apply the int32 vector/scalar step at offset 0
      of the input at the cursor, bridge it and concatenate it to the
      prefix; full-width partition lemmas (`*_u64` in
      `general-partition.click`) replace the signed outer metadata. A
      per-batch int32 proof with a join was tried first: the batch seeds
      would be the lane residues at batch entry, which a loop invariant can
      name only through the `bytes` array at another snapshot, and `simp`
      does not transport a specification nested in another one's seed.
      `write_slice` and `adler32_slice` no longer bridge, and they and both
      clients drop `len <= 2147483647u64`; their byte-preservation clauses
      are `forall (k: uint64) { k < len implies ... }`.
      `incremental-split.click` and most int32 partition lemmas are no
      longer used by any proof. Next: the C/Rust correspondence (stage 4
      prerequisites) and the constant-length computation contracts.
4. Last: delete the `int32` specification and the bridge, and drop the
   `_u64` suffix.

## Intended regression

- Remove the `<= 2147483647u64` preconditions from the adler2 public
  contracts (`public-general.click` and the other `public-*.click` files)
  and from the incremental and resumed clients, and keep them verifying
  (done).
- Do the same for the zlib canonical and full-stream proofs (done).
- State `adler_spec_a` at a `uint64` length above `INT32_MAX` without
  narrowing it (stage 1's nightly test does this for the byte sum; keep it
  when the suffix is dropped).

## Acceptance criteria

- The specification functions take a 64-bit length (or an `Integer` length
  with a 64-bit observation), and no proof narrows a `usize` or `z_size_t`
  count to `int32`.
- `bounded-count.click` and the `adler_bounded_*` lemmas are deleted or
  restated over `uint64`.
- The adler2, zlib and correspondence proofs verify, expand and re-verify
  over the full length range. The limit paragraphs in
  `design/adler32/project/adler2/README.md`, `design/adler32/project/zlib/README.md`
  and the "Left:" sentence in `design/typed-indices.md` are removed.
