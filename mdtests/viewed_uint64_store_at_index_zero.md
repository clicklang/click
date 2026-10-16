# A refused uint64 store names one source element

The missing ownership uses the store's actual width, including widths
other than the historical four-byte default.

```c filename=viewed_uint64_store_at_index_zero.c
void poke(uint64 *s) { s[0] = 7; }
```

```click
verifying "viewed_uint64_store_at_index_zero.c";

void poke(uint64* s) {
    views s[0..3];
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns s[0]`
```
