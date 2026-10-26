# A string literal stays read-only behind a cast

```c filename=c_const_cast_string_literal_write_rejected.c
int32 run(void) {
    char *p = (char *)"abc";
    p[0] = 65;
    return p[0];
}
```

```click
verifying "c_const_cast_string_literal_write_rejected.c";

int32 run() {
    ensures result == result;
}
```

```expect
fail: invalid memory access
```
