# Mixed-width owned entry segments

An empty function with two owned segments keeps entry work independent of
their numeric lengths, including a byte range of `INT32_MAX` elements beside
a 64-bit word.

```c filename=entry.c
void entry(unsigned long *word, unsigned char *bytes) {}
```

```click
verifying "entry.c";
void entry(uint64* word, uint8* bytes) {
    owns word[0..1];
    owns bytes[0..2147483647];
} by { execute(); }
```

```expect
pass
```
