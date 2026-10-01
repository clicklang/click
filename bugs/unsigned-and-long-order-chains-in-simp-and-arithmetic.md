# `simp` and `arithmetic()` stop at short order chains

## Violated invariant

Order reasoning should compose a chain of known facts the same way however
long it is, and unsigned chains the same way as signed ones. After PR #54 the
kernel's indexed order walk composes unsigned chains, but the surface tactics
still stop short:

- `simp` closes a three-edge *signed* chain through the `int32_*_transitive`
  theorems, but has no `uint32` counterparts, so a three-edge unsigned chain
  (`x <u a`, `a <=u b`, `b <=u 4u32` ⊢ `x <u 4u32`) fails.
- `arithmetic() using { … }` fails with three premises for signed and unsigned
  chains alike.
- The weakened bound `x <= 3u32` from `x < n`, `n <= 4u32` is not found
  (neither is the signed equivalent).

## Intended regression

An mdtest with a function whose `requires` give a three-edge chain, signed and
unsigned versions, each closed by `simp()` and by `arithmetic() using {…}`
listing the three premises; plus the weakened `<=` form. Negatives: the same
chains with one edge removed are refused.

## Acceptance criteria

- Three-edge (and longer) signed and unsigned chains close in `simp` and in
  `arithmetic() using`, with certificates the kernel checks.
- Mixed signed/unsigned chains still don't compose unless both ends are proven
  nonnegative.
- Work stays linear in the chain length (add a multi-size scaling check).
