# Numeric address facts alone cannot establish a pointer origin

The original numeric address premises are retained. Without a complete input-origin
promise, the nonzero integer-to-pointer conversion is refused.

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
fail: pointer_origin
```
