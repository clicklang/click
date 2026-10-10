# Dynamically viewable C-string witness for `strlen`

```c filename=cstr_dynamic_loadability.c
uint64 read_terminator(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_loadability.c";

uint64 read_terminator(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures result < 18446744073709551615u64;
} by {
    unfold(cstr_readable);
    execute();
    simp();
}
```

```expect
pass
```
