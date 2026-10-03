# An octal escape must fit one byte

```c filename=c_octal_escape_out_of_range_rejected.c
int32 value(void) {
    return '\400';
}
```

```click
verifying "c_octal_escape_out_of_range_rejected.c";

int32 value() {
    ensures true by auto;
}
```

```expect
fail:c_octal_escape_out_of_range_rejected.c:2: numeric character escape does not fit one byte
```
