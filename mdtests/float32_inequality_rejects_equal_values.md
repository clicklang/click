# Float inequality cannot prove that signed zeros differ

```click
theorem float32_zeros_differ() {
    ensures float32_from_bits(0) != float32_from_bits(0x80000000) by { close(); }
}
```

```expect
fail: could not establish `float32_from_bits(0x00000000) != float32_from_bits(0x80000000)`
```
