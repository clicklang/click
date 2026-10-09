# A helper's interior byte store cannot leave the caller's old scalar value

A symbolic signed integer cannot use the constant-only signed byte update.
Its byte store must still invalidate the caller's cached named value.

```c filename=inline_byte_write.c
static inline void overwrite(unsigned char *bytes) {
    bytes[1] = 7;
}
int64 mutate(int64 value) {
    int64 obj = value;
    overwrite((unsigned char *)(void *)&obj);
    return obj;
}
```

```click
verifying "inline_byte_write.c";
int64 mutate(int64 value) {
    ensures result == value;
} by { execute(); simp(); }
```

```expect
fail: result == value
```
