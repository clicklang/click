# The shared Adler-32 specification states lengths only up to `INT32_MAX`

Priority: P2.

Soundness: incomplete. Both checksum trials prove their results only for
inputs of at most 2,147,483,647 bytes, and refuse to state anything longer.
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

Widening the shared specification reaches a further proof-support gap in
`adler_byte_offset_association`. The signed version normalizes, but even an
explicit exact mathematical sum does not currently establish the corresponding
unsigned pointer equality:

```click
import click::integer;

theorem unsigned_offset_sum(bytes: uint8[], prefix: uint64,
                            suffix: uint64, total: uint64) {
 requires to_integer(total) == to_integer(prefix) + to_integer(suffix);
 ensures (bytes + prefix) + suffix == bytes + total by {
  normalize() using {
   to_integer(total) == to_integer(prefix) + to_integer(suffix);
  };
 }
}
```

This promptly reports that the goal did not normalize to true. The exact
Integer sum is significant: native wrapping equality alone would not justify
the address equality. Selected pointer-offset comparison reaches
`pointer_offsets_proven_equal_for_memory_resolution` in
`src/kernel/reasoning/memory_resolution.rs`; its unsigned rules do not cover
this general symbolic sum. This is missing proof support for the migration,
not a separate claim that `normalize()` violates its documented scope.
Coordinate that support with the thread owning pointer arithmetic/formation.
The original Rust chunk-tail proof passed after its separate cursor-restoration
fix; this prerequisite concerns the widened specification.

## Intended regression

- Remove the `<= 2147483647u64` preconditions from the adler2 public
  contracts (`public-general.click` and the other `public-*.click` files)
  and from the incremental and resumed clients, and keep them verifying.
- Do the same for the zlib canonical and full-stream proofs.
- Add an mdtest that states `adler_spec_a` at a `uint64` length above
  `INT32_MAX` and does not narrow it.

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
