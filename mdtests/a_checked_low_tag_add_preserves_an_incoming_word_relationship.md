# A checked low tag addition preserves an incoming word's pointer

```c filename=tag.c
struct node { int32 value; };
unsigned long blacken(unsigned long word) { return word + 1; }
```

```click
verifying "tag.c";
unsigned long blacken(unsigned long word) {
    requires (word & 1) == 0;
    ensures ((struct node*)(result & ~3)) == old((struct node*)(word & ~3));
} by { execute(); simp(); }
```
