# The stored value must have the cell's pointer type

A `struct other *` cannot be stored in a `struct node *` cell.

```c filename=c_pointer_cell_cast_wrong_value_rejected.c
struct node {
    unsigned long color;
    struct node *left;
};

struct other {
    int value;
};

void run(struct node *parent, struct other *new) {
    *(struct node **)&parent->left = new;
}
```

```click
verifying "c_pointer_cell_cast_wrong_value_rejected.c";

```

```expect
fail:c_pointer_cell_cast_wrong_value_rejected.c:11: cannot use `struct other *` where `struct node *` is required
```
