# Integer representation does not expose pointer representation bytes

```c filename=pointer_storage.c
void *keep(void *p) {
    void *saved = p;
    unsigned int *word = (unsigned int *)(void *)&saved;
    return saved;
}
```

```click
verifying "pointer_storage.c";
import click::integer;
void* keep(void* p) {
    ensures result == p;
} by {
    step_until(statement(2));
    have viewable(word[0..1]);
    apply(integer::uint32_from_le_bytes(word)) using {
        little_endian();
        viewable(word[0..1]);
    };
}
```

```expect
fail: defined
```
