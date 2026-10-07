# Clearing tag bits from a nonzero integer does not create pointer provenance

Knowing a loaded word's numeric value cannot invent a non-null allocation.
Clearing the low bits of 5 leaves 4, which has no originating pointer.

```c filename=tagged_pointer_nonzero_load_rejected.c
struct node { unsigned long word; };
struct node* forge(struct node* node) {
    unsigned long pc = node->word;
    return (struct node*)(pc & ~3);
}
```

```click
verifying "tagged_pointer_nonzero_load_rejected.c";
struct node* forge(struct node* node) {
    owns node->word;
    requires node->word == 5;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: integer-to-pointer cast requires a value that is a recorded pointer address or zero
```
