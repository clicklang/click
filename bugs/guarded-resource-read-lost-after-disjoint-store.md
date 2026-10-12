# A read exposed from a guarded resource is lost after a disjoint store

Soundness: incomplete. Click refuses a true fold: the guarded body's
field-value fact is not carried across a disjoint store. Nothing false is
accepted. Its priority comes from the rbtree subtree-size work it was
reduced from, not from soundness.

An unfolded resource's checked field-value fact must survive a write to a
separately owned field. Adding a proved nonnull guard around the same resource
body currently prevents refolding it after that write. Removing the guard
makes the unchanged C and all other contracts verify.

Small reproduction, reduced from rbtree subtree-size recomputation:

```c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    return value;
}
```

```click
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns ((struct cell*)(void*)p)->value;
        fact ((struct cell*)(void*)p)->value == number;
    }
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != (struct base*)(void*)root;
    ensures result == old(child.number);
    ensures child.number == old(child.number);
    ensures root->value == old(child.number);
} by { unfold(child); execute(); fold(child); simp(); }
```

The trace records the child's initial read equality, followed by the parent
field store. The failed fold asks for the same child read in a memory derived
from that store. The parent child-pointer field is borrowed and unchanged.
The nonnull and parent/child distinction are explicit, and the two value
fields are separately owned. No arithmetic is involved in this reduction.

Acceptance: preserve this guarded body's field-value fact through the disjoint
store; test the unconditional control and guarded form, source expansion,
negative cases that actually modify the selected field, and scope/withdrawal.
Determine why the existing framing path treats these equivalent exposed
bodies differently; do not add proof-only C or drop snapshot identity.
