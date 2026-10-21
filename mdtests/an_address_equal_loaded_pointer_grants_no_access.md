# An address-equal loaded pointer grants no access

C's `parent == p` compares addresses only. Separation may spell a range at an
address-equal coordinate, but ownership coverage needs full pointer equality,
so the write through `parent` stays refused even though `p` is owned.

```c filename=address-equal.c
struct node { uint64 tag; struct node *right; struct node *left; };
void f(struct node *p, struct node *g) {
    struct node *parent = g->left;
    if (parent == p) {
        parent->tag = 0;
    }
    return;
}
```

```click
verifying "address-equal.c";
void f(struct node *p, struct node *g) {
    owns *p;
    owns *g;
} by {
    execute();
}
```

```expect
fail: access outside the subobject the pointer designates
```
