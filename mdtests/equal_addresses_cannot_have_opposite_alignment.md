# Equal addresses cannot have opposite alignment

```c filename=alias.c
struct node { uint64 word; };
void impossible(struct node* p, struct node* q) {}
```

```click
verifying "alias.c";
void impossible(struct node* p, struct node* q) {
    requires p == q;
    requires aligned(p, 8);
    requires ((uint64)q & 7) != 0;
    ensures false;
} by { execute(); simp(); }
```

```expect
pass
```
