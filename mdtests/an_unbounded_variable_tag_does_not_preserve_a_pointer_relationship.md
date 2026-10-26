# An unbounded variable tag cannot establish the original pointer

```c filename=tag.c
struct slot { unsigned long word; };
void stamp(struct slot* slot, int32* p, int32 tag) {
    slot->word = (unsigned long)p | tag;
}
```

```click
verifying "tag.c";
void stamp(struct slot* slot, int32* p, int32 tag) {
    owns slot->word;
    requires aligned(p, 8);
    requires 0 <= tag;
    ensures ((slot->word & ~3) as (int32 *)) == p;
}
```

```expect
fail: ensures
```
