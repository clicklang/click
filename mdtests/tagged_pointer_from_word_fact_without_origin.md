# Numeric address facts alone cannot establish a pointer origin

The original numeric address premises are retained. Without a complete input-origin
promise, the nonzero integer-to-pointer conversion is refused.

```c filename=tagged_pointer_from_word_fact.c
struct node {
    int32 value;
    unsigned long word;
};

int32 recovers_parent(unsigned long word, struct node* next) {
    return (struct node*)(word & ~3) == next;
}

int32 color_is_black(unsigned long word, struct node* next) {
    return (word & 1) == 1;
}
```

```click
verifying "tagged_pointer_from_word_fact.c";

int32 recovers_parent(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 color_is_black(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer_origin
```
