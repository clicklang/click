# Stated separation decides complete C pointer comparisons and proof goals

```c filename=sep.c
struct node { unsigned long word; };
int apart_c(struct node *a, struct node *b) {
    if (a == b) return 1;
    return 0;
}
```

```click
verifying "sep.c";
int32 apart_c(struct node* a, struct node* b) {
    requires separate(memory(a->word), memory(b->word));
    ensures result == 0;
} by { execute(); simp(); }

theorem apart(a: struct node*, b: struct node*) {
    requires separate(memory(a->word), memory(b->word));
    ensures a != b by { assumption(); }
}

theorem apart_reversed(a: struct node*, b: struct node*) {
    requires separate(memory(a->word), memory(b->word));
    ensures b != a by { assumption(); }
}
```

```expect
pass
```
