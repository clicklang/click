# A current resource fold cannot use the entry pointer's ownership

```c filename=entry_resource.c
struct node { uint64 tag; };
void adopt(struct node *p, struct node *q) { p = q; }
```

```click
verifying "entry_resource.c";
resource tag_at(p: struct node*) { owns p->tag; }
void adopt(struct node* p, struct node* q) {
    consumes p->tag;
    ensures 1 == 1;
} by {
    step();
    fold(tag_at(p));
    execute(); simp();
}
```

```expect
fail: missing resource fact
```
