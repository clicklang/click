# A caller's C-string requirement reaches `strlen` through identity casts

A cast that leaves the pointer unchanged, to `const char *` or to
`unsigned char *` from `uint8 *`, names the same storage, so the caller's borrowed string
`cstr_at(bytes, _)` is the instance `strlen` views.

```c filename=strlen_casts.c
uint64 through_const_char(uint8 bytes[]) {
    uint64 n;
    n = strlen((const char *)bytes);
    return n;
}

uint64 through_unsigned_char(uint8 bytes[]) {
    uint64 n;
    n = strlen((unsigned char *)bytes);
    return n;
}
```

```click
verifying "strlen_casts.c";

uint64 through_const_char(uint8 bytes[]) {
    views str: click::cstr::cstr_at(bytes, _);
    ensures result == str.len;
    ensures bytes[result] == '\0';
} by {
    execute();
    simp();
}

uint64 through_unsigned_char(uint8 bytes[]) {
    views str: click::cstr::cstr_at(bytes, _);
    ensures result == str.len;
    ensures bytes[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
