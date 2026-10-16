# An identity cast does not invent a C-string requirement

Looking through a cast finds the caller's own string; without one, `strlen`
has no `cstr_at` instance to view.

```c filename=strlen_cast_unproved.c
uint64 unproved(uint8 bytes[]) {
    uint64 n;
    n = strlen((const char *)bytes);
    return n;
}
```

```click
verifying "strlen_cast_unproved.c";

uint64 unproved(uint8 bytes[]) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: call to `strlen` needs a held `cstr_at` instance to give `s.len` its value
```
