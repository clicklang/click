# A cast that views a pointer cell as an integer cell is rejected

The store would write an `unsigned long`, not the cell's pointer.

```c filename=c_pointer_cell_cast_scalar_cell_rejected.c
struct node {
    unsigned long color;
    struct node *left;
};

struct other {
    int value;
};

void run(struct node *parent, unsigned long value) {
    *(unsigned long *)&parent->left = value;
}
```

```click
verifying "c_pointer_cell_cast_scalar_cell_rejected.c";

```

```expect
fail:c_pointer_cell_cast_scalar_cell_rejected.c:11: incompatible C pointer types
```
