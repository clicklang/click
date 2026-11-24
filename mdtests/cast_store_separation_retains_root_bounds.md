# A cast store's separation goal retains root bounds

The write through `dst` has root bounds from the cast through `void *`.
`step() by` must present the separation goal with those same bounds.

```c filename=cast_store.c
struct node { int32 tag, left, right; };
struct extended { struct node base; int32 size; };

void put(struct node* a, struct node* b) {
    struct extended* dst = (struct extended*)(void*)b;
    dst->size = 1;
}
```

```click
verifying "cast_store.c";

void put(struct node* a, struct node* b) {
    owns (b as (void *) as (struct extended *))->size;
    views a->left;
    views a->right;
} by {
    step_until(statement(1).entry);
    step() by { close(); }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
