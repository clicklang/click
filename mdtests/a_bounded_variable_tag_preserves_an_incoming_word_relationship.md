# A bounded variable tag preserves an incoming word's pointer relationship

```c filename=tag.c
struct node { int32 value; };
unsigned long recolor(unsigned long word, int32 tag) {
    return (word & ~3) | tag;
}
```

```click
verifying "tag.c";
unsigned long recolor(unsigned long word, int32 tag) {
    requires 0 <= tag;
    requires tag <= 1;
    ensures ((struct node*)(result & ~3)) == old((struct node*)(word & ~3));
} by { execute(); simp(); }
```
