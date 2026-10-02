# A hexadecimal escape must fit one byte

```c filename=c_hex_escape_out_of_range_rejected.c
int32 value(void) {
    return '\x100';
}
```

```click
verifying "c_hex_escape_out_of_range_rejected.c";

int32 value() {
    ensures true by auto;
}
```

```expect
fail:c_hex_escape_out_of_range_rejected.c:2: numeric character escape does not fit one byte
```
