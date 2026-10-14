# A theorem applied after return blocks a returned instance fold

Soundness: incomplete. Click refuses a valid proof: the applied theorem is
checked and its conclusion is true, and the same proof verifies when the
`apply` is replaced by an equivalent `have` or moved before the fold. No false
acceptance is known; the refusal happens in return certification, which only
rejects.

Proof steps written after execution reaches function exit are deferred and
replayed against the return. From reading the code, a `have` there is
recorded as a checked return proposition (`record_return_proposition`), and a
theorem `apply` appears not to be. When a later step folds a produced
resource instance, return certification
(`checked_return_path` → `trace_completion` in
`src/kernel/proof/execution.rs`) finds the applied conclusion in the fold
proof's fact delta, cannot match it against the returning path, and refuses
with `return proof assumes an unjustified path fact`.

The diagnostic is also unusable. It names neither the unjustified fact nor
the tactic that introduced it, points at the final `simp();`, and
`click verify --trace-proof` prints `proof trace unavailable: no checked path
was retained for this failure` with or without `--trace-to`.

Reproduced on master `93bc0b8`:

````md
```c filename=pick.c
int32 pick(int32* p, int32 x) {
    *p = x;
    return x;
}
```

```click
spec enum Shape { Leaf, Pair(int32, int32) }
function first(s: Shape) -> int32 {
    match s {
        Shape::Leaf => 0,
        Shape::Pair(a, b) => a,
    }
}
theorem first_pair(a: int32, b: int32) {
    ensures first(Shape::Pair(a, b)) == a by { unfold(first(Shape::Pair(a, b))); normalize(); }
}
resource Cell(p: int32*) {
    field model: int32;
    owns p[0..1];
    fact p[0] == model;
}
verifying "pick.c";
int32 pick(int32* p, int32 x) {
    consumes p[0..1];
    produces c: Cell(p);
    ensures c.model == first(Shape::Pair(x, 3));
} by {
    execute();
    apply(first_pair(x, 3));
    let c = fold(Cell(p), { model: x });
    simp();
}
```
````

```text
proof error:
  could not certify return instance fold
  return proof assumes an unjustified path fact

tactic@35:
  simp();
```

Each of these one-line variants verifies: `apply` before `execute()`, the
`fold` before the `apply`, or `have first(Shape::Pair(x, 3)) == x by {
unfold(first(Shape::Pair(x, 3))); normalize(); }` in place of the `apply`.

Found while proving one general `__rb_erase_augmented` contract for
`examples/rbtree-erase` (design-review P5, R2 in
[design/proof-reuse.md](../design/proof-reuse.md#r2-one-general-contract-per-function)).
Each exit folds an outcome resource after the C returns, as the existing
`rbtree_erase_leaf_wrapper.click` folds its outputs. The same refusal
appeared at those exits. A temporary print of the rejected fact showed two
kinds: an applied lemma's algebraic equality (this reproduction), and a
four-byte `CMemoryLoadable` fact over a pointer field that a store had
materialized as one eight-byte cell. `is_loadable_concretely` accepts only the
exact stored width. A post-return `unfold` of a call-produced `ctx_at` before
the fold was refused with `instance rewrite introduced an unchecked fact`.
Those two are not yet reduced.

Acceptance:

- The reproduction verifies, as an mdtest that keeps the post-return `apply`
  followed by the fold.
- If a post-return step must be refused, the error names the unjustified fact
  in source form and the tactic that introduced it, and `--trace-proof`
  shows the path to it.
- Reduce and fix, or file separately, the partial-width loadable fact and the
  post-return `unfold` refusal.
