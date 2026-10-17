# A loop preserves the explicit packed-pointer relationship

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long word, struct node* p, int32 count) {
    int32 i = 0;
    while (i < count) {
        word = word | 1;
        i++;
    }
    return ((struct node*)(word & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long word, struct node* p, int32 count) {
    requires p != 0;
    requires 0 <= count;
    requires count <= 4;
    requires ((struct node*)(word & ~1)) == p;
    views p->value;
} by {
    step(); step();
    loop {
        decreases count - i;
        invariant 0 <= i;
        invariant i <= count;
        invariant ((struct node*)(word & ~1)) == p;
        initialize by { simp(); }
        preserve by { step(); step(); simp(); }
    }
    execute(); simp();
}
```

```expect
pass
```
