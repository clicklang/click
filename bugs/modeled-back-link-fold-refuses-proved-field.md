# A modeled back-link fold refuses a proved pointer-field fact

A no-op C function unfolds a model, retains the child's left link through a
plain resource, proves `qid->left == pid`, and folds a modeled resource with
that same fact. The fold rejects fact 2 of 2 of arm `At`. Repeated verification
reproduces the refusal on PR #596 and with the shared typed-read congruence
implementation. The analogous link to a separate model pointer is
accepted after PR #596; linking back to the modeled program parameter still
fails. Rebinding model pointers to proved program spellings must preserve
established readable field facts.

Save the following files together and run `click verify back-link.click`.
The expected result is success. The current result is:

```
fold requires the instance body facts for the proposed fields
fact 2 of 2 of arm `At` is not established
```

```c filename=back-link.c
struct node { struct node *tag; struct node *right; struct node *left; };
void recombine(struct node *p) { }
```

```click filename=back-link.click
verifying "back-link.c";
spec enum Triple { At(struct node*, struct node*, struct node*), }
resource pair(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns pid->left; owns qid->right; owns qid->left;
 fact p == pid; fact pid->left == qid; fact qid->left == pid;
 }, }
}
resource links(p: struct node*, child: struct node*) {
 owns p->left; owns p->right; fact p->left == child;
}
resource fields(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns qid->left; owns qid->right;
 fact p == qid; fact qid->left == pid;
 }, }
}
void recombine(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Triple::At(pid,qid,rid) => {
 unfold(tree);
 have p->left == qid by { simp(); }
 fold(links(qid,pid));
 unfold(links(qid,pid));
 have qid->left == pid by { assumption(); }
 let check = fold(fields(qid), { model: Triple::At(pid,qid,rid) });
 execute(); normalize();
 }, }
}
```

The goal lowers to `PointerOffsetEqual`. A registered read can be recovered
for its left offset, but the fold still does not establish the equality.
Check how the parameter alias, the recorded field value, and the current
read evidence reach the fold's proof context; do not assume a snapshot or block
equality from equal offsets, or scan unrelated proof history.

Acceptance: the unchanged no-op C and sidecar verify and pass default-budget
expansion audit. A wrong link target, missing address equality, and distinct
allocations still reject. Keep proof work local to the selected read and its
equality evidence, with a scaling regression if indexing changes.
