# A bounded variable tag keeps a stored pointer relationship

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
    requires tag <= 1;
    ensures ((int32*)(slot->word & ~3)) == p;
} by { execute(); simp(); }
```

```expect
pass
```
