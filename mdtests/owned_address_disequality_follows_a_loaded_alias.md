# A known separation reaches a C comparison through a loaded alias

```c filename=loaded-pointer-branch.c
struct node { uint64 word; struct node *right; };
int32 inspect(struct node *a, struct node *b) {
    struct node *tmp = b->right;
    if (a != tmp)
        return 1;
    return 0;
}
```

```click
verifying "loaded-pointer-branch.c";
int32 inspect(struct node *a, struct node *b) {
    owns a->word;
    owns b->word;
    owns b->right;
    requires b->right == b;
    ensures result == 1;
} by {
    step(); step();
    have tmp == b by assumption();
    have separate(memory(a->word), memory(b->word)) by assumption();
    have a != b by assumption();
    have a != tmp by assumption();
    step();
    execute(); simp();
}
```

```expect
pass
```
