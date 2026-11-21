# An indexed byte read cannot overlap the cursor update

```c filename=indexed_alias.c
void copy_byte(void) {
    unsigned char dst[2] = {7, 11};
    unsigned char *output = dst;
    const unsigned char *input = (unsigned char *)(void *)&output;
    *output++ = input[1];
}
```

```click
verifying "indexed_alias.c";

void copy_byte() {
    ensures true;
}
```

```expect
fail: unsequenced update
```
