# Byte strings require explicit encoding for non-ASCII text

```click
theorem unicode_needs_bytes() {
    ensures b"café" == List<uint8>::Nil;
}
```

```expect
fail: byte string literals use ASCII source characters
```
