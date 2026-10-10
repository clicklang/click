# An identity cast does not invent a C-string requirement

Looking through a cast finds the caller's own requirement; without one,
`strlen`'s precondition is still missing.

```c filename=strlen_cast_unproved.c
int32 unproved(uint8 bytes[]) {
    int32 n;
    n = strlen((const char *)bytes);
    return n;
}
```

```click
verifying "strlen_cast_unproved.c";

int32 unproved(uint8 bytes[]) {
    ensures 0 <= result;
} by {
    execute();
    simp();
}
```

```expect
fail: strlen precondition
```
