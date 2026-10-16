# A bounded native-word tag can precede the pointer in a bitwise OR

```c filename=tag.c
struct slot { unsigned long word; };
void stamp(struct slot* slot, int32* p, unsigned long tag) {
    slot->word = tag | (unsigned long)p;
}
```

```click
verifying "tag.c";
void stamp(struct slot* slot, int32* p, unsigned long tag) {
    owns slot->word;
    requires aligned(p, 8);
    requires tag <= 1;
    ensures ((int32*)(slot->word & ~3)) == p;
} by { execute(); simp(); }
```
