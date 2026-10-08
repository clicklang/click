# An ordinary recursive resource unfolds by its definition in authority mode

The list resource is recursive and declared without `authorized`, so it
reaches no population. Its unfold is checked by its definition, not as a
population member's body access.

```c filename=list_zero.c
struct node {
    int32 value;
    struct node* next;
};

int32 list_zero(struct node* node) {
    struct node* next;
    int32 result;
    next = node->next;
    if (next == 0) {
        return 0;
    }
    result = list_zero(next);
    return result;
}
```

```click resource_semantics=authority
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}

verifying "list_zero.c";

int32 list_zero(struct node* node) {
    decreases list(node);
    requires node != 0;
    views list(node);

    ensures result == 0;
} by {
    unfold(list(node));
    execute();
    simp();
}
```

```expect
pass
```
