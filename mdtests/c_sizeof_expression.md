# The operand of `sizeof(expression)` is not evaluated

Only the operand type is used. The assignment inside `sizeof` does not happen.

```c filename=c_sizeof_expression.c
struct node {
    unsigned long color;
    struct node *left;
    char tag;
};

int32 sizes(struct node *parent, int32 bump) {
    return sizeof((parent->left)) * 100 + sizeof(*&parent->left) * 10 + sizeof(parent->tag)
        + sizeof(bump = 5) * 1000 + bump;
}
```

```click
verifying "c_sizeof_expression.c";

int32 sizes(struct node* parent, int32 bump) {
    requires bump == 1;
    ensures result == 4882 by auto;
}
```

```expect
pass
```
