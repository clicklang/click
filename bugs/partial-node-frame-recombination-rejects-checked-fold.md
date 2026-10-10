# Recombining partially framed node fields loses owned memory

Reproduced on ca63dba1f and the complete-address displacement fix. No C
operation or helper is needed: unfold a modeled resource, prove its child-link
alias, fold and unfold the child's two links, then fold all three child fields.
The final fold refuses with `fold requires ownership of the complete instance
body`. The field ownership is present throughout.

Adding a proved child-link equality and changing a resource's grouping must
not remove ownership. A control with no explicit child-link `have`, or without
the intermediate `links` fold/unfold, verifies. Replacing the final modeled
instance with a plain composite instead reports `kernel rejected checked
resource fold: resource rewrite does not match the selected composite
definition`. The original reduction with an intervening helper also fails.

Save these files together and run `click verify recombine.click`.

```c filename=recombine.c
struct node { struct node *tag; struct node *right; struct node *left; };
void recombine(struct node *p) {}
```

```click filename=recombine.click
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
 have p->left == qid by { simp(); }
 fold(links(qid));
 unfold(links(qid));
 let check = fold(fields(qid), { model: Identity::At(qid) });
 unfold(check);
 execute(); normalize();
 }, }
}
```

Inspect selected memory consumption after the intermediate unfold, including
pointer-read alias normalization and the resource equality index. Preserve the
exact owned byte footprints and alias evidence; do not accept a rewrite solely
because the producer reports success.

Acceptance: the proof and default-budget audit pass; missing or overlapping
ownership still rejects; checking remains local to the selected resources.
Recheck the propagated red-sibling rotation context fold that motivated this
reduction. Remove this file when the fix and regressions land.
