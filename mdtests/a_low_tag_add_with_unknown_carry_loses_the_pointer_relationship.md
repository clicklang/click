# An unchecked tag addition may carry into pointer address bits

```c filename=tag.c
struct node { int32 value; };
unsigned long blacken(unsigned long word) { return word + 1; }
```

```click
verifying "tag.c";
unsigned long blacken(unsigned long word) {
    ensures ((struct node*)(result & ~3)) == old((struct node*)(word & ~3));
} by { execute(); simp(); }
```

```expect
fail: ensures
```
