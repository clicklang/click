# A range over a symbolic number of structs is not usable

## Violated invariant

A range on a struct pointer counts structs. `views p[0..n]` with `0 <= i` and
`i < n` covers `p[i]`, so a read of `p[i].y` has the access it needs. Click
accepts the clause but cannot use it unless the count is a constant.

## Reproduction

```c
struct pt { int x; int y; };
int first(struct pt *p, int n) { return p[0].y; }
int at(struct pt *p, int n, int i) { return p[i].y; }
```

```click
verifying "sn.c";

int32 first(struct pt* p, int32 n) {
    requires n >= 1;
    views p[0..n];
    ensures result == p[0].y;
} by { execute(); simp(); }
```

fails at setup with "segment end may have undefined behavior the facts do not
rule out: signed overflow". Adding `requires n <= 1000;` moves the failure to
the read: "held `views p[0..(2 * n)]` covers `p[1..2]` only when
`2 <= (2 * n)`".

```click
int32 at(struct pt* p, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1000;
    views p[0..n];
} by { execute(); simp(); }
```

fails with "missing resource fact `views p[i].y`".

With a constant count (`views p[0..2];` and a read of `p[1].y`) the proof
verifies.

## Cause

Memory is held in runs of one scalar element type. A struct has several
fields, so a struct range has no single run. The parser lowers
`p[lo..hi]` on a struct pointer to four-byte `int32` cells by multiplying each
bound by the struct's cell count (`parse_current_contract_segments_inner` in
`src/surface/parser.rs`). The multiplied bound can overflow, the checker does
not derive `2 <= 2 * n` from `1 <= n`, and a field of element `i` is not
matched to a cell of the run.

This is not new. Before ranges counted structs, the same C needed the cells
written by hand (`views p[0..2 * n]`) and failed the same way. Counting
structs moved the multiplication into the parser.

A struct-array parameter (`struct item items[2]`) keeps the struct as its
element, but only for constant bounds: `memory_with_symbolic_loadable_cells`
in `src/surface/lowering/resource_lowering.rs` enumerates the elements from
`start` to `end`.

One mdtest wrote `viewable(node[0..n])` for `n` cells to make `node->left`
readable. It now names the field
(`mdtests/contract_nested_dynamic_viewable_composite_argument.md`).

## Directions

- One run per scalar field, at the field's offset, with the struct's size as
  the stride and the unscaled bounds. This needs a run whose stride differs
  from its element width.
- Or an iterated clause over whole elements,
  `forall k where 0 <= k and k < n { owns p[k]; }`, which needs `p[k]` on a
  struct pointer as a place. Today that base evaluation reports that the
  pointer arithmetic left the pointed-to object.

## Intended regression

The two reproductions as mdtests expecting `pass`, with a struct that has
fields of two widths, and a variant of `at` with `i <= n` expecting refusal.

## Acceptance

- Both reproductions verify without a bound on `n`.
- The `i <= n` variant is refused.
- A range on a struct pointer reaches the kernel without a multiplied bound.
