# Numeric address facts alone cannot establish a pointer origin

The original numeric address premises are retained. Without a complete input-origin
promise, the nonzero integer-to-pointer conversion is refused.

```c filename=tagged_pointer_from_field_fact.c
struct node {
    int32 value;
    unsigned long word;
};

int32 parent_value(struct node* node, struct node* next) {
    struct node* parent = (struct node*)(node->word & ~3);
    return parent->value;
}
```

```click
verifying "tagged_pointer_from_field_fact.c";

int32 parent_value(struct node* node, struct node* next) {
    requires node != 0;
    requires next != 0;
    requires aligned(next, 8);
    requires node->word == address(next) + 1;
    views node->word;
    views next->value;
    ensures result == next->value;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer_origin
```
