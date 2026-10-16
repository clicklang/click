# A pointer typedef is written as its type in a head

A head writes a scalar or struct typedef name of the verified source, but not
an alias of a pointer type; it writes that parameter's C type instead.

```c filename=main.c
typedef struct node { int value; } *node_ptr;

int node_value(node_ptr node) {
    return node->value;
}
```

```click
verifying "main.c";

int node_value(node_ptr node) {
    views node->value;
    ensures result == node->value;
} by {
    execute();
    simp();
}
```

```expect
fail: the typedef `node_ptr` stands for a pointer
```
