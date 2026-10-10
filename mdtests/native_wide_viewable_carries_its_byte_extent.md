# Native wide viewable carries its byte extent

```c filename=native_wide_viewable_carries_its_byte_extent.c
void hold(const unsigned int *values, unsigned long length) {}
```

```click
verifying "native_wide_viewable_carries_its_byte_extent.c";
void hold(const uint32* values, uint64 length) {
 requires viewable(values[0u64..length]);
 ensures 1 == 1;
} by {
 have length <= 2305843009213693951u64 by assumption();
 execute(); simp();
}
```

```expect
pass
```
