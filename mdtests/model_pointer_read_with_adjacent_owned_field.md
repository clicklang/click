# A model pointer alias retains all owned fields

Owning an additional field of the same child must not hide the field read
through its C cursor. The model identity and cursor are explicitly equal.

```c filename=read-right.c
struct node { struct node *tag; struct node *right; struct node *left; };
struct node *read_right(struct node *p) { struct node *q = p->left; return q->right; }
```

```click
verifying "read-right.c";
spec enum Pair { At(struct node*, struct node*), }
resource pair(p: struct node*) {
 field model: Pair;
 match model { Pair::At(pid,qid) => {
 owns pid->left; owns qid->right; owns qid->tag;
 fact p == pid; fact pid->left == qid;
 }, }
}
struct node *read_right(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Pair::At(pid,qid) => {
 unfold(tree);
 have p->left == qid by { simp(); }
 step(); step();
 have q == qid by { simp(); }
 execute(); normalize();
 }, }
}
```

```expect
pass
```
