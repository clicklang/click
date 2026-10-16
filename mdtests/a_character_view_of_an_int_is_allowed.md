# A character view of an `int` is allowed

A character type may read the bytes of any object (C11 6.5p7), so reading a
declared `int` through an `unsigned char *` is not an aliasing violation,
though the reverse, an `int` read of a byte buffer, is.

```c filename=bytes.c
unsigned char low_byte(void) {
    int value = 258;
    unsigned char *b = (unsigned char *)(void *)&value;
    return b[0];
}
```

```click
verifying "bytes.c";

uint8 low_byte() {
    ensures result == 2u8;
} by {
    execute();
    simp();
}
```

```expect
pass
```
