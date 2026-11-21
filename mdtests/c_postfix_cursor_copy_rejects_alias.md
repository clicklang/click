# A byte cannot alias a cursor it is updating

A byte read through the source cursor can alias an interior byte of the
destination cursor itself. The write to that cursor is unsequenced with
the read.

```c filename=cursor_alias.c
void copy_byte(void) {
    unsigned char dst[2] = {7, 11};
    unsigned char *output = dst;
    const unsigned char *input = (unsigned char *)(void *)&output + 1;
    *output++ = *input++;
}
```

```click
verifying "cursor_alias.c";

void copy_byte() { ensures true; }
```

```expect
fail: unsequenced update
```
