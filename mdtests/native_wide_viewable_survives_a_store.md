# Native wide liveness survives a store

```c filename=native_wide_viewable_survives_a_store.c
unsigned int put(const unsigned char *bytes, unsigned long length, unsigned int *cell) { *cell = 1; return 1; }
```

```click
verifying "native_wide_viewable_survives_a_store.c";
uint32 put(const uint8* bytes, uint64 length, uint32* cell) {
 requires length <= 2147483647u64;
 views bytes[0..length];
 owns cell[0..1];
 ensures result == 1u32;
} by {
 step();
 have viewable(bytes[0u64..length]) by {
  transport(at(function.entry, viewable(bytes[0u64..length])), viewable(bytes[0u64..length])) using { at(function.entry, viewable(bytes[0u64..length])); }
 }
 execute(); simp();
}
```

```expect
pass
```
