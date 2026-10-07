# Pointer arithmetic past an object of unknown size is accepted without an obligation

## Violated invariant

C11 6.5.6p8: adding an integer to a pointer is defined only when the result
points at an element of the same array object or one past its end; otherwise
the behavior is undefined. Click refuses `a + 3` for a local `int32 a[2]`
(`CUndefinedBehavior::PointerArithmetic`) and `q + 2` for a 4-byte `malloc`
block, but when the pointed-to block has no recorded size, which is every
pointer parameter, `pointer_block_bounds`
(`src/kernel/eval/operators.rs:2520-2527`) returns `Some(Vec::new())`:

```rust
let Some(block_size) = state.memory().block_size(&pointer.block).cloned() else {
    return Some(Vec::new());
};
```

so `pointer_offset_by_elements_paths` (`operators.rs:2277-2282`) attaches no
formation guard and no proof obligation. The displaced pointer is produced on a
normal path. The caller's `owns`/`views` range, the only extent information
the function has, is consulted only to *extend* the materialized bound
(`pointer_is_in_memory_resource`), never to bound the formation. A function
whose only path forms `p + 1000` while holding `views p[0..4]` therefore
verifies, and the result pointer can be compared (`q != p` evaluates to 1)
and offset back (`(p + 1000) - 1000` dereferences as `p[0]`), all on a path C
leaves undefined.

## Reproduction

```c filename=repro.c
int32 f(int32 *p) { int32 *q = p + 1000; return q != p; }
```

```click
verifying "repro.c";

int32 f(int32 *p) {
    views p[0..4];
    ensures result == 1;
} by { execute(); simp(); }
```

Observed: `1 selected proof verified` (exit 0). Variants that also verify:
`int32 *q = p + 1000; return 0;` with `owns p[0..4]`; `int32 *q = p - 1;`;
`int32 *q = p + i;` with `i` unconstrained; and
`int32 *q = p + 1000; int32 *r = q - 1000; return *r;` with
`ensures result == p[0]`. The displaced pointer is only refused when it is
dereferenced (`missing resource fact views p[1000..1001]`) or when the
cumulative element index overflows `int32` (`p + 2147483647` then `+ 1`).

## Intended regression

The reproduction above, expected to fail with `undefined behavior: pointer
arithmetic left the pointed-to object` or with a missing-prerequisite
obligation that the formed pointer lies inside an owned or viewed range
(`0 <= 1000 <= 4` is false). A positive companion: `int32 *q = p + 4;`
(one past the viewed range) with `views p[0..4]` must still verify, and
`p + i` with `requires 0 <= i && i <= 4` must verify.

## Acceptance criteria

- Forming `p + k` from a pointer whose block size is unknown owes an
  obligation that the result lies within some range the state holds for that
  block (an `owns`/`views` range, inclusive of its one-past end), or is
  refused as `PointerArithmetic` when the facts decide it lies outside every
  such range.
- Displacing by zero and forming the one-past-end pointer of a held range
  remain accepted.
- Documentation (`docs/concepts/undefined-behavior.md`, the C0 reference)
  states the rule for pointers of unknown object size.
