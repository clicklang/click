# A pointer field survives separate writes through an alias

The recorded pointer read must cross discarded cache cells without losing
the value written through the equal parent address. The Linux rotation pattern
still writes the other node and then the parent tag.

```c filename=alias-frame.c
struct node { uint64 tag; struct node *right; struct node *left; };
void alias_frame(struct node *p, struct node *n, struct node *g) {
    struct node *parent = g->left;
    parent->right = 0;
    n->left = parent;
    parent->tag = 0;
    return;
}
```

```click
verifying "alias-frame.c";
void alias_frame(struct node *p, struct node *n, struct node *g) {
    owns *p;
    owns *n;
    owns *g;
    requires g->left == p;
    ensures p->right == 0;
} by {
    step(); step(); step(); mark stored;
    step(); step();
    transport(at(stored, parent->right == 0), p->right == 0) using {
        at(stored, parent->right == 0);
        parent == p;
        at(stored, parent) == p;
        separate(memory(parent->right), memory(n->left));
        separate(memory(parent->right), memory(parent->tag));
    };
    execute(); assumption();
}
```

```expect
pass
```
