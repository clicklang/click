# Fold resource arguments lose model-pointer alias facts

## Violated invariant

A resource argument may read an owned field through a pointer proved equal to
its owner. After unfolding a modeled node, `have id->left == 0 by simp`
verifies, but `fold(empty(id->left), ...)` refuses the same read with
`could not lower resource empty argument 0: missing pure fact` and empty fact
lists. Replacing only that fold argument with `p->left` verifies. The C is
unchanged. Reproduced on the rbtree successor branch based on `6f32740ed`.

This blocks refolding empty children in the first red-parent erase-color
case. The proof can establish the unchanged child links after both color
writes; the subsequent resource-argument lowering loses their alias evidence.

## Reduced regression

Save these as `probe.c` and `probe.click`, then run `click verify probe.click`.

```c
struct Node { unsigned long tag; struct Node *left; };
void put(struct Node *p) { p->tag = 0; }
```

```click
verifying "probe.c";
spec enum Model { At(struct Node*) }
resource node(p: struct Node*) {
 field model: Model;
 match model { Model::At(id) => { owns p->tag; owns p->left; fact p == id; fact p->left == 0; }, }
}
resource empty(p: struct Node*) { field model: int32; fact model == 0; fact p == 0; }
void put(struct Node* p) {
 consumes n: node(p);
 produces p->tag; produces p->left;
 produces e: empty(p->left);
 ensures 1 == 1;
} by {
 match n.model { Model::At(id) => {
  unfold(n); step();
  have id->left == 0 by { simp(); }
  let e = fold(empty(id->left), { model: 0 });
  execute(); simp();
 }, }
}
```

The control changes `fold(empty(id->left),` to `fold(empty(p->left),`.
Both use the existing ownership and checked `p == id` fact; neither grants
new read authority.

## Acceptance criteria

- The original reduced proof verifies and its smart tactics expand and replay.
- Resource-argument lowering retains the relevant checked alias facts and
  still requires typed read authority; a mismatched or unowned node is refused.
- The rbtree erase-color prototype can fold its empty child resource through
  the selected model pointer after the color writes.
- Use indexed facts already present at the fold; do not scan execution history
  or assume the resource body facts the fold is meant to prove.
