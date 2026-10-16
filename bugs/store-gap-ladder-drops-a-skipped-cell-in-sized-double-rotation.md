# Store-gap ladder drops a skipped cell in the sized double rotation

Priority: P2.

Soundness: not soundness as observed. A debug build asserts a kernel invariant
and aborts. Release builds verify the same proof. The invariant protects memory
reasoning, so a dropped cell could lose a fact, not invent one. No false
acceptance is known.

The violated invariant is in `check_gap_kept_cells`
(`src/kernel/reasoning/store_gap.rs`). A store that skips a cell by its
constant byte gap must keep that cell in the ladder. Debug builds re-check the
cells at each end of a skipped range. Here the ladder drops one:

```text
a store at Pointer { block: Symbolic(Variable(1000000)), offset: Constant(0) }
skipped the cell at Pointer { block: Symbolic(Variable(1000000)), offset:
Constant(8) } by its constant byte gap, but the ladder drops it
```

## Reproduction

Build a debug `click`, then run
`click verify examples/rbtree-augmented/rbtree_size_insert_double_rotation.click`.
The `mirrored` file fails the same way. The `NIGHTLY` example test runs these
files in a debug test build, so the nightly run fails here.

The assertion first fires with clicklang/click#1180 ("C pointer comparisons
state address equality only"). At `992812e2`, just before it, with the
separation fix from this branch applied, both files verify in a debug build.

## Acceptance criteria

- Both double-rotation files verify in a debug build with the C and the proof
  unchanged.
- A gate-sized regression asserts that the ladder keeps every skipped cell for
  a store into a fresh symbolic block. It covers the shape here: an 8-byte
  cell after a store at offset 0, after a C pointer comparison that states
  only address equality.
