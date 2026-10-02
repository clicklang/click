# A cast that retypes the pointer cell is rejected

The cell holds a `struct node *`; viewing it as a `struct other *` cell would be a different object type.

```c filename=c_pointer_cell_cast_other_struct_rejected.c
struct node {
    unsigned long color;
    struct node *left;
};

struct other {
    int value;
};

void run(struct node *parent, struct other *new) {
    *(struct other **)&parent->left = new;
}
```

```click
verifying "c_pointer_cell_cast_other_struct_rejected.c";

```

```expect
fail:c_pointer_cell_cast_other_struct_rejected.c:11: incompatible C pointer types
```
