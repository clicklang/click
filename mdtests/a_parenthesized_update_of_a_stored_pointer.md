# A compound update can advance a pointer stored in memory

The byte cursor advances to its one-past endpoint and backs up before reading.
The integer cursor advances in units of the pointee type.

```c filename=cursor_advance.c
int advance_byte(unsigned char **str, unsigned char *buffer, unsigned char length)
{
    unsigned char *start = buffer;
    *str = start;
    *str += length;
    (*str)--;
    return **str;
}

int advance_int(int **slot, int *buffer)
{
    *slot = buffer;
    ++*slot;
    *slot += 1;
    *slot -= 1;
    return **slot;
}
```

```click
verifying "cursor_advance.c";

int advance_byte(uint8** str, uint8* buffer, uint8 length) {
    owns str[0..1];
    views buffer[0..4];
    requires length == 4;
    ensures result == buffer[3];
}

int advance_int(int32** slot, int32* buffer) {
    owns slot[0..1];
    views buffer[0..2];
    ensures result == buffer[1];
}
```

```expect
pass
```
