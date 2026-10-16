# A refused uint16 store names one source element

The missing ownership uses the store's actual width, including widths
other than the historical four-byte default.

```c filename=viewed_uint16_store_at_index_zero.c
void poke(uint16 *s) { s[0] = 7; }
```

```click
verifying "viewed_uint16_store_at_index_zero.c";

void poke(uint16* s) {
    views s[0..3];
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns s[0]`
```
