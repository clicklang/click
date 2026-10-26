# An unchecked tag addition may carry into pointer address bits

```c filename=tag.c
struct node { int32 value; };
unsigned long blacken(unsigned long word) { return word + 1; }
```

```click
verifying "tag.c";
unsigned long blacken(unsigned long word) {
    ensures ((result & ~3) as (struct node *)) == old((word & ~3) as (struct node *));
}
```

```expect
fail: ensures
```
