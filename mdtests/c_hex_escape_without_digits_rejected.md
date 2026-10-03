# A hexadecimal escape needs a digit

```c filename=c_hex_escape_without_digits_rejected.c
int32 value(void) {
    return '\x';
}
```

```click
verifying "c_hex_escape_without_digits_rejected.c";

int32 value() {
    ensures true by auto;
}
```

```expect
fail:c_hex_escape_without_digits_rejected.c:2: hexadecimal character escape `\x` requires at least one digit
```
