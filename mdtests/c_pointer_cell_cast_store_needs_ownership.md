# The cast store still needs write authority for the cell

Spelling the store through a cast grants nothing.

```c filename=c_pointer_cell_cast_store_needs_ownership.c
struct node {
    unsigned long color;
    struct node *left;
};

struct other {
    int value;
};

void write_once(struct node *parent, struct node *new) {
    *(volatile typeof(parent->left) *)&(parent->left) = (new);
}
```

```click
verifying "c_pointer_cell_cast_store_needs_ownership.c";

void write_once(struct node* parent, struct node* new) {
    views &parent->left;
    ensures parent->left == new by auto;
}
```

```expect
fail: missing resource fact `owns
```
