# A uint64 index's high word cannot alias an owned byte

An index whose low word is zero still denotes a different element. The
order bridge must require a representable range before using that low word.

```c filename=uint64_index_high_word_cannot_alias_byte.c
void write(unsigned char* bytes, unsigned long index) {
    bytes[index] = 9;
}
```

```click
verifying "uint64_index_high_word_cannot_alias_byte.c";
void write(uint8* bytes, uint64 index) {
    requires index == 4294967296u64;
    owns bytes[0..1];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
