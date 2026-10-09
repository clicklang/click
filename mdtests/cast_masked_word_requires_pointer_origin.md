# A cleared word with an exact pointer address

Clearing low bits alone gives an arbitrary integer no pointer origin.
Without an exact address premise the cast must be refused.

```c filename=cast_masked_word_requires_pointer_origin.c
struct node { int32 value; };
struct node *clear_tag(unsigned long word, struct node *p) {
    return (struct node *)(word & ~3);
}
```

```click
verifying "cast_masked_word_requires_pointer_origin.c";
struct node* clear_tag(unsigned long word, struct node* p) {
    ensures result == p;
} by { execute(); simp(); }
```

```expect
fail: integer without pointer origin cannot become a pointer
```
