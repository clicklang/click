# A function head writes pointer typedef names

A pointer alias stands for its pointer type in a function head. A `const`
written before the alias qualifies the pointer itself, as in C, and the
alias's own pointee qualification is kept.

```c filename=main.c
typedef struct node { int value; } *node_ptr;
typedef const int *int_view;

int node_value(const node_ptr node) {
    return node->value;
}

int first(int_view values) {
    return values[0];
}

void set_value(node_ptr node, int value) {
    node->value = value;
}
```

```click
verifying "main.c";

int node_value(const node_ptr node) {
    views node->value;
    ensures result == node->value;
} by {
    execute();
    simp();
}

int first(int_view values) {
    views values[0];
    ensures result == values[0];
} by {
    execute();
    simp();
}

void set_value(node_ptr node, int value) {
    owns node->value;
    ensures node->value == value;
} by {
    execute();
    simp();
}
```

```expect
pass
```
