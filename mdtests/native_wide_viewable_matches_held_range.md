# Native wide viewable matches held range

```c filename=native_wide_viewable_matches_held_range.c
void hold(const unsigned char *bytes, unsigned long length) {}
void window(const unsigned char *bytes, unsigned long lo, unsigned long hi) {}
```

```click
verifying "native_wide_viewable_matches_held_range.c";
void hold(const uint8* bytes, uint64 length) {
 requires length <= 2147483647u64;
 views bytes[0..length];
} by {
 have viewable(bytes[0u64..length]) by assumption();
 execute(); simp();
}
void window(const uint8* bytes, uint64 lo, uint64 hi) {
 requires lo <= hi;
 requires hi <= 2147483647u64;
 views bytes[lo..hi];
} by {
 have viewable(bytes[lo..hi]) by assumption();
 execute(); simp();
}
```

```expect
pass
```
