# Recombining model pointer fields preserves ownership

A checked pointer alias and an intermediate resource grouping preserve the owned node fields.

```c filename=recombine.c
struct node { struct node *tag; struct node *right; struct node *left; };
void recombine(struct node *p) {}
```

```click
verifying "recombine.c";
spec enum Pair { At(struct node*, struct node*), }
resource pair(p: struct node*) {
 field model: Pair;
 match model { Pair::At(pid,qid) => {
 owns pid->left; owns pid->tag; owns qid->right; owns qid->tag; owns qid->left;
 fact p == pid; fact pid->left == qid;
 }, }
}
resource links(p: struct node*) { owns p->left; owns p->right; }
spec enum Identity { At(struct node*), }
resource fields(p: struct node*) {
 field model: Identity;
 match model { Identity::At(id) => { owns id->tag; owns id->left; owns id->right; fact p == id; }, }
}
void recombine(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Pair::At(pid,qid) => {
 unfold(tree);
 have p->left == qid;
 fold(links(qid));
 unfold(links(qid));
 let check = fold(fields(qid), { model: Identity::At(qid) });
 unfold(check);
 execute(); normalize();
 }, }
}
```

```expect
pass
```
