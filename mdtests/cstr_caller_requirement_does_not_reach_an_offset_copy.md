# A caller's C-string requirement does not reach a copy that points elsewhere

`p = bytes + 1` is not the pointer of the caller's string
`cstr_at(bytes, _)`, so `strlen(p)` finds no string at `p` to view.

```c filename=cstr_offset_copy.c
uint64 offset(uint8 bytes[]) {
    uint8* p;
    p = bytes + 1;
    return strlen(p);
}
```

```click
verifying "cstr_offset_copy.c";

uint64 offset(uint8 bytes[]) {
    views str: click::cstr::cstr_at(bytes, _);
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: call to `strlen` needs a held `cstr_at` instance to give `s.len` its value
```
