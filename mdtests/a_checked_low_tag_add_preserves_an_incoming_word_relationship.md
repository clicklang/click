# A checked low tag addition preserves an incoming word's pointer

```c filename=tag.c
struct node { int32 value; };
unsigned long blacken(unsigned long word) { return word + 1; }
```

```click
verifying "tag.c";
unsigned long blacken(unsigned long word) {
    requires (word & 1) == 0;
    ensures ((result & ~3) as (struct node *)) == old((word & ~3) as (struct node *));
}
```

```expect
pass
```
