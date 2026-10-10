# A caller's C-string requirement reaches `strlen` through identity casts

A cast that leaves the pointer unchanged, to `const char *` or to
`unsigned char *` from `uint8 *`, names the same storage, so the caller's
`cstr_readable(bytes)` still discharges `strlen`'s precondition.

```c filename=strlen_casts.c
int32 through_const_char(uint8 bytes[]) {
    int32 n;
    n = strlen((const char *)bytes);
    return n;
}

int32 through_unsigned_char(uint8 bytes[]) {
    int32 n;
    n = strlen((unsigned char *)bytes);
    return n;
}
```

```click
verifying "strlen_casts.c";

int32 through_const_char(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures bytes[result] == '\0';
} by {
    execute();
    simp();
}

int32 through_unsigned_char(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures bytes[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
