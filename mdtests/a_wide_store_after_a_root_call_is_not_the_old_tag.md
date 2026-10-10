# a wide store after a root call is not the old tag

A rotation-shaped walk loads two child links, rewires one, calls a helper
that moves a named root context, reloads through the moved cursor, and stores
zero into the eight-byte `tag` it reaches. `near == rid` makes the current
read of `near->tag` congruent with `rid->tag`, but the store means it is not
the tag `rid` held before the write. The wide-read rule compares both reads'
memory histories and stored values in both directions, so claiming the old
value is refused. This catches a wide-read congruence that equates a fresh
store with the overwritten value.

```c filename=a_wide_store_after_a_root_call_is_not_the_old_tag.c
struct node { unsigned long tag; struct node *left; struct node *right; };
struct root { struct node *node; };
void helper(struct node *p, struct node *q, struct root *root) { root->node = q; }
void probe(struct node *p, struct root *root) {
    struct node *cursor = p->right;
    struct node *near = cursor->left;
    p->right = near;
    helper(p, cursor, root);
    cursor = near;
    near = cursor->right;
    near->tag = 0;
}
```

```click
verifying "a_wide_store_after_a_root_call_is_not_the_old_tag.c";
spec enum Leaf { At(struct node*) }
spec enum Branch { At(struct node*, Leaf) }
spec enum Outer { At(struct node*, Branch) }
resource leaf(p: struct node*) {
 field model: Leaf;
 match model { Leaf::At(id) => { owns p->tag; fact p == id; } }
}
resource branch(p: struct node*) {
 field model: Branch;
 match model { Branch::At(id, lm) => {
  owns p->right; owns child: leaf(p->right);
  fact p == id; fact child.model == lm;
 } }
}
resource shell(p: struct node*) {
 field model: Outer;
 match model { Outer::At(id, bm) => {
  owns p->left; owns child: branch(p->left);
  fact p == id; fact child.model == bm;
 } }
}
spec enum Context { Top }
resource context(p: struct node*, root: struct root*) { field model: Context; match model { Context::Top => { owns root->node; fact root->node == p; } } }
void helper(struct node *p, struct node *q, struct root *root) {
 consumes before: context(p, root);
 produces after: context(q, root);
} by { match before.model { Context::Top => { unfold(before); execute(); let after = fold(context(q, root), {model: Context::Top}); simp(); } } }
void probe(struct node *p, struct root *root) {
 owns p->right;
 consumes b: shell(p->right); consumes c: context(p, root);
 ensures 1 == 1;
} by {
 match b.model { Outer::At(sid, bm) => {
 match bm { Branch::At(nid, lm) => {
 match lm { Leaf::At(rid) => {
  let {child: near_tree} = unfold(b);
  let {child: far_tree} = unfold(near_tree);
  unfold(far_tree);
  have p->right == sid;
  have sid->left == nid;
  have nid->right == rid;
  step(); step(); step(); step(); step();
  let { after: c } = step(helper(p, cursor, root), { before: c });
  step();
  have cursor == nid;
  have cursor->right == rid;
  step();
  have near == rid;
  mark before_write;
  step();
  have near->tag == at(before_write, rid->tag) by { normalize() using { near == rid; } }
  execute(); simp();
 } }
 } }
 } }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
