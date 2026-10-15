# Dynamic C-string reads require an explicit permission range

`cstr::readable` and `viewable` describe safe contents, but neither one grants
the resource-sensitive permission needed by an actual C array read.

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
fail: missing resource fact `views bytes
```
