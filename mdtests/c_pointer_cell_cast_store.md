# A store through a cast to a pointer cell writes that cell

The Linux `WRITE_ONCE(x, value)` macro expands to `*(volatile typeof(x) *)&(x) = (value);`. For a struct-pointer field that is a store to the field's own pointer cell through a pointer of the cell's own type, with or without the `volatile` qualifier and the `typeof` spelling. A cast to `struct node **` points to a pointer cell, not to a struct, so the store is not an aggregate copy.

```c filename=c_pointer_cell_cast_store.c
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

void spelled(struct node *parent, struct node *new) {
    *(struct node * volatile *)&parent->left = new;
}

void plain(struct node *parent, struct node *new) {
    *(struct node **)&parent->left = new;
}

struct node *read_back(struct node *parent, struct node *new) {
    *(typeof(parent->left) *)&(parent->left) = new;
    return parent->left;
}
```

```click
verifying "c_pointer_cell_cast_store.c";

void write_once(struct node* parent, struct node* new) {
    owns &parent->left;
    ensures parent->left == new by auto;
}

void spelled(struct node* parent, struct node* new) {
    owns &parent->left;
    ensures parent->left == new by auto;
}

void plain(struct node* parent, struct node* new) {
    owns &parent->left;
    ensures parent->left == new by auto;
}

struct node* read_back(struct node* parent, struct node* new) {
    owns &parent->left;
    ensures result == new by auto;
}
```

```expect
pass
```
