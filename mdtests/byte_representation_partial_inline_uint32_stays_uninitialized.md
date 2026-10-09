# A helper's partial byte writes cannot initialize its caller's scalar

The return-frame refresh must preserve the caller's uninitialized binding.

```c filename=partial_inline_word.c
static inline void fill(unsigned char *bytes) {
    bytes[0] = 17;
    bytes[1] = 128;
    bytes[2] = 238;
}
unsigned int decode(void) {
    unsigned int obj;
    fill((unsigned char *)(void *)&obj);
    return obj;
}
```

```click
verifying "partial_inline_word.c";
uint32 decode() {
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: uninitialized
```
