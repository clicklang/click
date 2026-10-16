# A refused byte store names only its byte at index 0

A read-only byte range cannot authorize a store. The refusal names the
single byte required by the unchanged C statement.

```c filename=viewed_byte_store_at_index_0.c
void poke(uint8 *s) { s[0] = 7; }
```

```click
verifying "viewed_byte_store_at_index_0.c";

void poke(uint8* s) {
    views s[0..3];
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns s[0]`
```
