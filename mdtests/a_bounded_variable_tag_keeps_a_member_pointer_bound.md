# Clearing a bounded variable tag preserves a member's bound

```c filename=tag.c
struct pair { int32 first; int32 second; };
int32 read_sibling(struct pair* p, int32 tag) {
    unsigned long word = (unsigned long)&p->first | tag;
    return ((int32*)(word & ~3))[1];
}
```

```click
verifying "tag.c";
int32 read_sibling(struct pair* p, int32 tag) {
    views p->first;
    views p->second;
    requires aligned(&p->first, 8);
    requires 0 <= tag;
    requires tag <= 1;
} by { execute(); simp(); }
```

```expect
fail: outside the subobject
```
