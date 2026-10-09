# A call loses an unchanged pointer fact after named resource unfolds

A call must preserve a separately owned pointer cell outside its write footprint,
including ownership exposed by unfolding named resources. In this reproduction,
`p->left == 0` verifies after the two stores but fails immediately after `retarget`.
The same C verifies when the caller declares the node fields flat and requires
`p->left == 0`, instead of consuming and opening the two `links` instances.

Save this C as `stores.c`:

```c
struct node { uint64 tag; struct node *right; struct node *left; };
void retarget(struct node *p, struct node *q, int32 *anchor) {}
void call(struct node *p, struct node *q, int32 *anchor) { p->right = 0; q->left = p; retarget(p, q, anchor); }
```

```click
verifying "stores.c";
resource links(p: struct node*) {
    field model: int32;
    owns p->tag; owns p->left; owns p->right;
    fact p->left == 0;
}
resource cursor(p: struct node*, anchor: int32*) { field tag: int32; owns *anchor; }
void retarget(struct node* p, struct node* q, int32* anchor) {
    consumes a: cursor(p, anchor);
    owns p->tag;
    owns q->tag;
    produces b: cursor(q, anchor);
    ensures b.tag == old(a.tag);
} by {
    unfold(a);
    let b = fold(cursor(q, anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(struct node* p, struct node* q, int32* anchor) {
    consumes c: cursor(p, anchor);
    consumes x: links(p);
    consumes y: links(q);
    produces p->tag; produces p->left; produces p->right;
    produces q->tag; produces q->left; produces q->right;
    produces *anchor;
    ensures p->left == 0;
} by {
    unfold(x); unfold(y);
    have separate(memory(p->left), memory(q->left)) by { assumption(); }
    step(); step();
    have p->left == 0 by { simp(); }
    mark before;
    let { b: c } = step(retarget(p, q, anchor), { a: c });
    have p->left == 0 by { simp(); }
    unfold(c);
    execute(); simp();
}
```

The failure says a store to `anchor` may have changed the pointer. The called C
body is empty; its contract permits changes to the anchor and two tags, not the
caller's `p->left`. A fresh produced binder reproduces the larger erase proof's
failure too, so name reuse alone does not explain it.

Acceptance: verify and audit this source unchanged, keep a negative that rejects
an actual pointer overwrite, and preserve full pointer widths and initialization
authority. Avoid whole-context scans and history-dependent work per unrelated
resource. The reduced caller should need no extra frame bookkeeping.
