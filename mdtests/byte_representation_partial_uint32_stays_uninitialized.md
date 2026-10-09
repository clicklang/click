# Three byte writes do not initialize a four-byte integer

An unwritten fourth byte cannot be invented by permission or an integer load.

```c filename=partial_word.c
unsigned int decode(void) {
    unsigned int obj;
    unsigned char *bytes = (unsigned char *)(void *)&obj;
    bytes[0] = 17;
    bytes[1] = 128;
    bytes[2] = 238;
    return obj;
}
```

```click
verifying "partial_word.c";
uint32 decode() {
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: uninitialized
```
