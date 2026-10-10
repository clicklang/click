# A modeled fold loses a pointer-field fact preserved by its resource frame

Reproduced with the complete-address relative interval index, which repairs
an earlier ownership refusal and exposes this fact-checking refusal. The C
function is a no-op. The proof unfolds a model, proves its parent link, folds
and unfolds a plain resource retaining the child's left link, and checks that
link with `assumption()`. Folding a modeled resource with the same owned links
and fact then refuses:

```
fold requires the instance body facts for the proposed fields
fact 2 of 2 of arm `At` is not established
```

The second fact is `qid->left == rid`, checked immediately before the fold.
Rebinding a constructor pointer to an equal program spelling must preserve
its readable field value. This is not permission to omit the fact or weaken
the C claim. A version with an actual child load and a modular tag-copy helper
also fails. A no-op parent with all three node fields and a selected child
resource passed during reduction, so declared memory grouping affects the
refusal. A control using explicit pointer parameters for the target resource’s
memory and link fact, instead of its matched constructor pointers, verifies.

Save the files together and run `click verify model-link-no-load.click`.

```c filename=model-link-no-load.c
struct node { struct node *tag; struct node *right; struct node *left; };
void recombine(struct node *p) { }
```

```click filename=model-link-no-load.click
verifying "model-link-no-load.c";
spec enum Triple { At(struct node*, struct node*, struct node*), }
resource pair(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns pid->left; owns qid->right; owns qid->left;
 fact p == pid; fact pid->left == qid; fact qid->left == rid;
 }, }
}
resource links(p: struct node*, child: struct node*) {
 owns p->left; owns p->right; fact p->left == child;
}
resource fields(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns qid->left; owns qid->right;
 fact p == qid; fact qid->left == rid;
 }, }
}
void recombine(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Triple::At(pid,qid,rid) => {
 unfold(tree);
 have p->left == qid by { simp(); }
 fold(links(qid,rid));
 unfold(links(qid,rid));
 have qid->left == rid by { assumption(); }
 let check = fold(fields(qid), { model: Triple::At(pid,qid,rid) });
 execute(); normalize();
 }, }
}
```

Inspect the modeled binding's selected pointer spelling and logical field
read. `memory_address_spelling` currently asks `pointer_at_constant_base`, whose
constant-displacement check uses affine block coordinates rather than the
whole-address equality available to `pointer_at_base`; verify whether this
misses the selected field's retained spelling before changing that path.

Acceptance: the fold and default-budget audit pass; a wrong link value and a
missing pointer alias still reject. Keep equality and lookup local to the
selected address and resource. Recheck the propagated red-sibling context's
child-argument refusal without assuming it is identical until established.
