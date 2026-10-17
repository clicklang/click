# Clearing tag bits from a nonzero integer does not create pointer provenance

Knowing a loaded word's numeric value cannot invent a non-null allocation.
Clearing the low bits of 5 can name the opaque address 4. Returning that
value grants no allocation; dereferencing it still requires a full pointer
relationship and memory permission.

```c filename=tagged_pointer_nonzero_load_rejected.c
struct node { unsigned long word; };
struct node* forge(struct node* node) {
    unsigned long pc = node->word;
    return (struct node*)(pc & ~3);
}
unsigned long read_forged(struct node* node) {
    unsigned long pc = node->word;
    return ((struct node*)(pc & ~3))->word;
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
unsigned long read_forged(struct node* node) {
    owns node->word;
    requires node->word == 5;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
