# A whole stored packed word keeps its carrier

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long word, unsigned long* slot, struct node* p) {
    *slot = word;
    unsigned long copied = *slot;
    return ((struct node*)(copied & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long word, unsigned long* slot, struct node* p) {
    requires p != 0;
    requires ((word & ~1) as (struct node *)) == p;
    owns *slot;
    views p->value;
    ensures result == p->value;
}
```

```expect
pass
```
