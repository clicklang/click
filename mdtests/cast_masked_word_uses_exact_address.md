# A cleared word with an exact pointer address

The cast uses the checked address equation for the complete masked expression.
An opaque input word must not prevent that exact lookup.

```c filename=cast_masked_word_uses_exact_address.c
struct node { int32 value; };
struct node *clear_tag(unsigned long word, struct node *p) {
    return (struct node *)(word & ~3);
}
```

```click
verifying "cast_masked_word_uses_exact_address.c";
struct node* clear_tag(unsigned long word, struct node* p) {
    requires (word & ~3) == address(p);
    ensures result == p;
} by { execute(); simp(); }
```

```expect
pass
```
