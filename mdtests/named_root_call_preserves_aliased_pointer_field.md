# Preserve a child pointer after a rotation store

```c filename=probe.c
struct node { unsigned long tag; struct node *right; struct node *left; };
struct root { struct node *node; };
void helper(struct node *p, struct node *q, struct root *root) { root->node = q; }
void probe(struct node *p, struct root *root) {
    struct node *cursor = p->right;
    struct node *near = cursor->left;
    p->right = near;
    cursor->left = p;
    helper(p, cursor, root);
    cursor = near;
    near = cursor->left;
    cursor->left = 0;
    near->right = cursor;
}
```

```click
verifying "probe.c";
spec enum Leaf { At(struct node*) }
spec enum Branch { At(struct node*, Leaf) }
spec enum Outer { At(struct node*, Branch) }
resource leaf(p: struct node*) {
 field model: Leaf;
 match model { Leaf::At(id) => { owns p->tag; owns p->left; owns p->right; fact p->left == 0; fact p->right == 0; fact p == id; } }
}
resource branch(p: struct node*) {
 field model: Branch;
 match model { Branch::At(id, lm) => {
  owns p->left; owns child: leaf(p->left);
  fact p == id; fact child.model == lm;
 } }
}
resource shell(p: struct node*) {
 field model: Outer;
 match model { Outer::At(id, bm) => {
  owns p->tag; owns p->left; owns child: branch(p->left);
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
 owns p->tag; owns p->right;
 consumes b: shell(p->right); consumes c: context(p, root);
 ensures 1 == 1;
} by {
 match b.model { Outer::At(sid, bm) => {
 match bm { Branch::At(nid, lm) => {
 match lm { Leaf::At(rid) => {
  let {child: near_tree} = unfold(b);
  let {child: far_tree} = unfold(near_tree);
  unfold(far_tree);
  have p->right == sid by { simp(); }
  have sid->left == nid by { simp(); }
  have nid->left == rid by { simp(); }
  have rid == p->right->left->left by { normalize() using { p->right == sid; sid->left == nid; nid->left == rid; } }
  have nid == p->right->left by { normalize() using { p->right == sid; sid->left == nid; } }
  have separate(memory(p->right->left->left->left), memory(p->right->left->left)) by { assumption(); }
  have separate(memory(rid->left), memory(nid->left)) by { transport(separate(memory(p->right->left->left->left), memory(p->right->left->left)), separate(memory(rid->left), memory(nid->left))) using { separate(memory(p->right->left->left->left), memory(p->right->left->left)); rid == p->right->left->left; nid == p->right->left; }; }
  step(); step(); step(); step(); step(); step();
  let { after: c } = step(helper(p, cursor, root), { before: c });
  step();
  have cursor == nid by { simp(); }
  have cursor->left == rid by { simp(); }
  step();
  have near == rid by { simp(); }
  have rid->left == 0 by { simp(); }
  mark before_detach;
  step();
  have rid->left == 0 by { transport(at(before_detach, rid->left) == 0, rid->left == 0) using { at(before_detach, rid->left) == 0; separate(memory(rid->left), memory(nid->left)); cursor == nid; near == rid; }; }
  have separate(memory(rid->left), memory(near->right)) by { transport(separate(memory(rid->left), memory(rid->right)), separate(memory(rid->left), memory(near->right))) using { separate(memory(rid->left), memory(rid->right)); near == rid; }; }
  mark before_attach;
  step();
  have near->right == cursor by { simp(); }
  have rid->right == cursor by { transport(near->right == cursor, rid->right == cursor) using { near->right == cursor; near == rid; }; }
  have rid->left == 0 by { transport(at(before_attach, rid->left) == 0, rid->left == 0) using { at(before_attach, rid->left) == 0; separate(memory(rid->left), memory(near->right)); near == rid; }; }
  execute(); simp();
 } }
 } }
 } }
}
```

```expect
pass
```
