# `sizeof` of a struct-valued expression is rejected

Only scalar and pointer operands are modeled; use `sizeof(struct node)`.

```c filename=c_sizeof_struct_expression_rejected.c
struct node {
    unsigned long color;
};

int32 size(struct node *parent) {
    return sizeof(*parent);
}
```

```click
verifying "c_sizeof_struct_expression_rejected.c";

```

```expect
fail:c_sizeof_struct_expression_rejected.c:6: `sizeof` of an expression requires a modeled scalar or pointer operand
```
