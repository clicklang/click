# A cleared word with an exact pointer address

Clearing low bits alone gives an arbitrary integer no pointer origin.
The cast can name an opaque pointer, but without a full representation
premise it cannot identify that pointer with `p`.

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
fail: unclosed goal: result == p
```
