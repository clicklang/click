# Pointer equality across one sibling-field store

An ordinary pointer claim uses the shared graph after a write to a separate
field. The explicit normalization step must expand and independently recheck.

```c filename=read_store.c
struct node { struct node *left; int tag; };
struct node *touch(struct node *p) { p->tag = 1; return p->left; }
```

```click
verifying "read_store.c";
struct node* touch(struct node* p) {
 owns &p->left;
 owns &p->tag;
 ensures result == old(p->left);
} by {
 step();
 have p->left == old(p->left) by { normalize() using {} }
 execute();
 simp();
}
```

```expect
pass
```
