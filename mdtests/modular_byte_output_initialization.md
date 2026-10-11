# Modular byte output initializes the caller's storage

The fixed output range must be completely written by the helper. The byte
caller checks a value postcondition; the word caller checks that its previously
unwritten integer can be read. This safety claim does not assert reconstruction
of the word value from the helper's four specification byte reads.

```c filename=output.c
void fill(unsigned char* p) {
    p[0] = 120;
    p[1] = 86;
    p[2] = 52;
    p[3] = 18;
}
unsigned char first(void) {
    unsigned int obj;
    unsigned char* bytes = (unsigned char*)(void*)&obj;
    fill(bytes);
    return bytes[0];
}
unsigned int word(void) {
    unsigned int obj;
    unsigned char* bytes = (unsigned char*)(void*)&obj;
    fill(bytes);
    return obj;
}
```

```click
verifying "output.c";
void fill(uint8* p) {
    owns p[0..4];
    ensures initialized(p[0..4]);
    ensures p[0] == 120u8;
    ensures p[1] == 86u8;
    ensures p[2] == 52u8;
    ensures p[3] == 18u8;
} by { execute(); simp(); }
uint8 first() { ensures result == 120u8; } by { execute(); simp(); }
uint32 word() { ensures result == result; } by { execute(); simp(); }
```

```expect
pass
```
