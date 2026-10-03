# A cast that views an integer field as a pointer cell is rejected

The `typeof` names one field and the address another, so the store would not be to the same kind of cell.

```c filename=c_pointer_cell_cast_wrong_field_rejected.c
struct node {
    unsigned long color;
    struct node *left;
};

struct other {
    int value;
};

void run(struct node *parent, struct node *new) {
    *(volatile typeof(parent->left) *)&(parent->color) = (new);
}
```

```click
verifying "c_pointer_cell_cast_wrong_field_rejected.c";

```

```expect
fail:c_pointer_cell_cast_wrong_field_rejected.c:11: incompatible C pointer types
```
