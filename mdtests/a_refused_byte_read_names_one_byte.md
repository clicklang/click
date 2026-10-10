# A refused byte read names one byte

A read of one `uint8` outside every held range is refused, and the refusal
names the one element the read needs, `bytes[0]`, not four bytes.

```c filename=a_refused_byte_read_names_one_byte.c
unsigned char one(const unsigned char *bytes) { return bytes[0]; }
```

```click
verifying "a_refused_byte_read_names_one_byte.c";
uint8 one(const uint8* bytes) {
    views bytes[1..2];
    ensures result == bytes[0];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views bytes[0]`
```
