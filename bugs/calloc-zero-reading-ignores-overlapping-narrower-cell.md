# A calloc zero reading ignores a narrower cell stored inside the loaded range

## Violated invariant

A load reads the bytes a store wrote. `calloc` memory "reads as zero or null
until overwritten" (`docs/concepts/memory-model.md`), and "memory keeps one
description of any byte" (`docs/internals/byte-representation.md`). A store
of a narrower value strictly inside a wider load's byte range overwrites some
of the bytes that load reads, so the load is no longer zero.

The C load path in `evaluate_c_memory_load_case`
(`src/kernel/eval/memory_loads.rs:995`) consults
`CMemory::is_zeroed_heap_address` (`src/kernel/primitives/memory_state.rs:2690`)
after the exact-address cell lookups (`memory.known_value(&pointer)` and the
resolution-equal scan) miss, and before `is_loadable_concretely`. Neither the
lookups nor `is_zeroed_heap_address` ask whether a *different-address* cell
overlaps the loaded bytes. A one-byte store at `b[5]` of a `calloc`ed
`int32[4]` records a `uint8` cell at offset 5; the later four-byte load at
offset 4 finds no cell at offset 4, finds the allocation still zeroed, and
returns `0`. The true value is `9 << 8`.

The same path answers an `int16` store inside an `int32` load, a byte store
inside an `int64` load, a byte store inside a pointer load (which then reads
as the canonical null pointer, so `q[0] == 0` is decided true), and a byte
store inside a struct field. It also answers the mirror image, a *wider*
cell that contains the load: an `int64` store of `1 << 40` at offset 0
followed by the `int32` load at offset 4 reads `0` (true value `256`), and an
`int32` store at offset 4 of a `calloc`ed pointer array followed by the
pointer load at offset 0 reads null. A store at the load's *exact* address
is refused as a load that does not fit the cell, and a byte store at a
symbolic index is refused too; but a symbolic-index *load* (`p[k]`,
`0 <= k < 4`) after the constant byte store is again answered `0`, because
the whole-allocation `zeroed_allocations` entry needs no constant offset. On `malloc` memory the same sequence is refused as an uninitialized
read, and when an `int32` cell already exists the byte view edits it in
place, so the hole is specific to the zero-reading fallback.

## Reproduction

```c filename=h7d.c
int32 f() {
    int32* p = calloc(4, sizeof(int32));
    if (p == 0) { return 0; }
    uint8* b = (uint8*)(void*) p;
    b[5] = 9;
    int32 r = p[1];
    free(p);
    return r;
}
```

```click
verifying "h7d.c";

int32 f() {
    ensures result == 0;
} by { execute(); simp(); }
```

Observed on 2026-10-07 with `click verify`: exit 0, `1 selected proof
verified`. `f` returns `2304` on the successful path.

Variants that also verify a false claim (each exit 0, reproduced on
2026-10-07): `i2_calloc_int16_store` (`int16` store at byte 2, `int32`
load at 0 claims `0`), `i7_calloc_byte_then_int64` (byte store at 5, `int64`
load at 0 claims `0`), `i8_calloc_ptr_byte` (byte store at 3 of a `calloc`ed
pointer array, `q[0] == 0` claims true), `i11_calloc_struct_byte` (byte store
at 1, `s->a` claims `0`), `m1_calloc_wide_store_narrow_load` (`int64` store
at 0, `int32` load at 4 claims `0`), `m4_calloc_ptr_int32_store` (`int32`
store at 4, pointer load at 0 claims null), `o3_calloc_byte_store_sym_load`
(byte store at 5, `p[k]` for `0 <= k < 4` claims `0`),
`p3_calloc_join_byte` (the byte store under an `if`, so one executed path
carries it), and `h7c_calloc_bytestore_realloc` (the same through a
`realloc` that preserves the zeroed prefix).

Controls that behave correctly: `i1` (byte store at the load's exact
address: refused as not fitting), `i12` (byte store at a symbolic index:
refused), `i4` and `i5` (an `int32` cell already present: the byte view
edits it and the stale claim is refused), `i9` (a seeded file-scope array
instead of `calloc`: refused), `p1` and `p4` (the byte store inside a loop
or a callee: the havoc drops the zero reading and the claim is refused).

## Intended regression

An mdtest with the C above whose `ensures result == 0` is refused, plus a
positive companion whose null path returns `2304` as well and whose
`ensures result == 2304` verifies (it is refused today with `left side evaluated to 0`, so it discriminates
the fix; `result == 0 or result == 2304` does not, since the buggy `0`
satisfies it), and one of the `int16`, `int64`, or pointer variants. A kernel test in
`src/kernel/tests/byte_view_tests.rs` (or beside
`zeroed_heap_with_cell` in `memory_state.rs`) that stores a one-byte cell
strictly inside a zeroed allocation and checks that a wider load covering it
is not answered as zero.

## Acceptance criteria

- A zeroed-allocation load is answered as zero only when no recorded cell
  overlaps any byte of `[offset, offset + width)`; an overlapping narrower
  cell either feeds the byte view (when the load's type has one and the
  other bytes are zero) or refuses the load as not fitting the cell.
- The same rule covers the zeroed prefix a successful `realloc` carries.
- The existing `calloc` positives (`mdtests/calloc_zeroed_int32.md`,
  `mdtests/realloc_preserves_calloc_prefix.md`, the join and loop negatives)
  keep their verdicts, and `scripts/check.sh` passes.
