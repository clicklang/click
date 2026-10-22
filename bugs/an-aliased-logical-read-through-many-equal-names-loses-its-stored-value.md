# An aliased logical read through many equal names loses its stored value

A logical `int32` read through a pointer known equal to the owner of a
stored cell should resolve to the stored value, however many other names
that pointer has and however many unrelated frames the context admits.

## Reproduction

The nightly scaling test
`kernel::eval::memory_loads::tests::scaling_tests::logical_read_address_uses_class_index_without_scanning_aliases_or_frames`
(`src/scaling_tests/kernel/eval/memory_loads/tests.rs`) fails on `master`
(`511f799f7`) and on `93f441928`, before the incremental contradiction
index:

```sh
RUST_MIN_STACK=8388608 cargo nextest run --lib --run-ignored all \
  logical_read_address_uses_class_index_without_scanning_aliases_or_frames
```

```text
assertion `left == right` failed
  left: Value(Int32(Variable(Variable(1349817021868))))
 right: Value(Int32(Constant(7)))
```

The context assumes `owner == alias`, stores `7` at `owner + 0`, `+ 4`,
and `+ 8`, and then adds `size` unrelated owned frames and `size` further
names `alias == v_i`. `logical_memory_load_address` still returns the
owner's address, but `evaluate_logical_memory_load_paths` reads a fresh
variable instead of the stored `7`.

## Violated invariant

A read whose address resolves to a stored cell reads that cell's value.
Losing it costs completeness, not soundness: the read becomes an unknown
value.

## Acceptance criteria

- The scaling test passes in the nightly suite, at every size it measures,
  with its work bound unchanged.
- If the cause is a gate-visible change, a gate test at one small size
  covers the stored value, so the regression is caught before nightly.
