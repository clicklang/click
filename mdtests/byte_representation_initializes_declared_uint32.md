# Four character writes initialize the declared unsigned integer

The integer starts uninitialized. The helper writes its little-endian bytes
through an ordinary character pointer, in a different call frame. The typed
observation must agree with the four bytes written by the helper.

```c filename=initialize_word.c
static inline void fill(unsigned char *bytes) {
    bytes[3] = 255;
    bytes[1] = 128;
    bytes[0] = 17;
    bytes[2] = 238;
}
unsigned int decode(void) {
    unsigned int obj;
    unsigned char *bytes = (unsigned char *)(void *)&obj;
    fill(bytes);
    return obj;
}
```

```click
verifying "initialize_word.c";
uint32 decode() {
    ensures result == 4293820433u32;
} by { execute(); simp(); }
```

```expect
pass
```
