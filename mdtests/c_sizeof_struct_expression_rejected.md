# `sizeof` of a struct-valued expression uses its aggregate layout

The operand is unevaluated: obtaining the record size does not load through `parent`.

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

int32 size(struct node* parent) { ensures result == 8; }

```

```expect
pass
```
