# A cast contract names a complete packed-pointer relationship

The precondition supplies designation and selected bounds explicitly, without
an auxiliary numeric address equation. A whole local copy keeps the carrier.

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long word, struct node* p) {
    unsigned long copied = word;
    return ((struct node*)(copied & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long word, struct node* p) {
    requires p != 0;
    requires ((struct node*)(word & ~1)) == p;
    views p->value;
    ensures result == p->value;
} by { execute(); simp(); }
```

```expect
pass
```
