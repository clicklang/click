# Dynamic C-string reads require an explicit permission range

`cstr::readable` and `viewable` describe safe contents, but neither one grants
a resource. `strlen` views a `cstr_at` instance, and a caller that holds only
the predicate has none to lend it, so the call is refused before the C array
read that would need a permission as well.

```c filename=cstr_dynamic_indexed_read_requires_permission.c
int32 read_terminator_without_permission(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_indexed_read_requires_permission.c";

int32 read_terminator_without_permission(uint8 bytes[]) {
    requires click::cstr::readable(bytes);
    ensures result == '\0' by {
        unfold(click::cstr::readable);
        execute();
        simp();
    }
}
```

```expect
fail: call to `strlen` needs a held `cstr_at` instance to give `s.len` its value
```
