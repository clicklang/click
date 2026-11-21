# A byte copy with two postfix cursor updates

Both byte addresses come from the old cursor values. The destination cursor
can also be addressed elsewhere, as it is in cJSON's string parser.

```c filename=cursor_copy.c
void copy_cursors(unsigned char *output, const unsigned char *input) {
    *output++ = *input++;
}

int copy_byte(void) {
    unsigned char src[2] = {3, 5};
    unsigned char dst[2] = {7, 11};
    const unsigned char *input = src;
    unsigned char *output = dst;
    unsigned char **cursor = &output;
    *output++ = *input++;
    return dst[0] + 10 * **cursor + 100 * *input;
}
```

```click
verifying "cursor_copy.c";

void copy_cursors(uint8* output, const uint8* input) {
    owns output[0..1];
    views input[0..1];
    ensures output[0] == old(input[0]);
}

int32 copy_byte() {
    ensures result == 613;
}
```

```expect
pass
```
