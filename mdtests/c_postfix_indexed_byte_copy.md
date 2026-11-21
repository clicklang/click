# A byte copy reads a constant index before storing through a postfix cursor

```c filename=indexed_copy.c
int copy_byte(void) {
    unsigned char src[2] = {3, 5};
    unsigned char dst[2] = {7, 11};
    const unsigned char *input = src;
    unsigned char *output = dst;
    *output++ = input[1];
    return dst[0] + 10 * *output + 100 * *input;
}
```

```click
verifying "indexed_copy.c";

int32 copy_byte() {
    ensures result == 415;
}
```

```expect
pass
```
