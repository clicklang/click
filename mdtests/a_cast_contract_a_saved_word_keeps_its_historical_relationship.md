# A saved word keeps its relationship after its source is overwritten

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long* slot, struct node* p) {
    unsigned long saved = *slot;
    *slot = 0;
    return ((struct node*)(saved & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long* slot, struct node* p) {
    requires p != 0;
    requires ((struct node*)(*slot & ~1)) == p;
    owns *slot;
    views p->value;
} by { execute(); simp(); }
```

```expect
pass
```
