# Numeric address facts alone cannot establish a pointer origin

The original numeric address premises are retained. Without a complete input-origin
promise, the nonzero integer-to-pointer conversion is refused.

```c filename=tagged_pointer_unmasked_cast_with_zero_tag.c
struct node {
    int32 value;
    unsigned long word;
};

int32 red_parent_is(unsigned long word, struct node* next, uint64 color) {
    return (struct node*)word == next;
}
```

```click
verifying "tagged_pointer_unmasked_cast_with_zero_tag.c";

int32 red_parent_is(unsigned long word, struct node* next, uint64 color) {
    requires word == address(next) + color;
    requires color == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer_origin
```
