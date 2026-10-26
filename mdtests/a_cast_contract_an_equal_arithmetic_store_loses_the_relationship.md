# An arithmetic store loses bounds even when the bits stay equal

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long* slot, struct node* p) {
    *slot = *slot + 0;
    unsigned long saved = *slot;
    return ((struct node*)(saved & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long* slot, struct node* p) {
    requires p != 0;
    requires ((*slot & ~1) as (struct node *)) == p;
    owns *slot;
    views p->value;
}
```

```expect
fail: access outside the subobject the pointer designates
```
