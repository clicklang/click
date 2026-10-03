# Dropping `const` does not grant write authority

A write through a cast pointer still needs an owned footprint; a `views`
borrow is not enough.

```c filename=c_const_cast_needs_write_authority.c
int32 set(const int *view) {
    int *p = (int *)view;
    *p = 7;
    return *view;
}
```

```click
verifying "c_const_cast_needs_write_authority.c";

int32 set(const int32* view) {
    views view[0..1];
    ensures result == 7 by auto;
}
```

```expect
fail: missing resource fact `owns view[0..1]`
```
