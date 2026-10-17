# Allocating and releasing N heap objects is quadratic

Soundness: not soundness. This is a performance defect: verifying a function
that allocates and then releases N heap objects takes time quadratic in N.
No verdict changes.

## Violated invariant

Simple checking must scale with the selected source and the state it changes
(`docs/internals/verification-efficiency.md`). Each allocation or release
step touches one object, so verifying N of each should take time roughly
linear in N.

## Reproduction

`scripts/step-scaling-hunt.py`'s `heap_objects` shape, with the profiling
build:

```sh
cargo build --profile profiling --bin click
python3 scripts/step-scaling-hunt.py heap_objects --sizes 32,64,128
```

Then generate N = 256 (`SHAPES["heap_objects"](256)`) and run
`target/profiling/click verify` on it. On master at `8d8a621c`:

| N   | whole verification | charged step work (total) |
|-----|--------------------|---------------------------|
| 32  | 0.42 s             | 123,012                   |
| 64  | 1.08 s             | 260,420                   |
| 128 | 2.89 s             | 578,244                   |
| 256 | 11.77 s            | —                         |

Time grows ×4.07 from 128 to 256 (exponent about 2), while charged work grows
only ×2.1 to ×2.2 per doubling, so most of the growth is uncharged. The
largest single step's charged work also doubles from N = 64 to 128
(2,121 to 3,839).

## Acceptance criteria

- Whole verification time grows at most about ×2.3 per doubling of N from 64
  to 256.
- A deterministic regression charges the growing work (or removes it), so a
  scaling test fails on the current behavior.
