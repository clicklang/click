# A postfix copy cannot treat an address-exposed parameter as value-only

Even when a nested block has already lowered the copy, a later use of the
parameter's address rules out the value-only treatment.

```c filename=cursor_parameter.c
void copy_byte(unsigned char *output, const unsigned char *input) {
    {
        *output++ = *input++;
    }
    unsigned char **cursor = &output;
}
```

```click
verifying "cursor_parameter.c";

void copy_byte(uint8* output, const uint8* input) {
    owns output[0..1];
    views input[0..1];
}
```

```expect
fail: cannot take the address of postfix copy cursor parameter
```
