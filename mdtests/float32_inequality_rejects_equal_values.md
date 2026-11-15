# Float inequality cannot prove that signed zeros differ

```click
theorem float32_zeros_differ() {
    ensures float32_from_bits(0) != float32_from_bits(0x80000000) by { normalize(); }
}
```

```expect
fail: goal did not normalize to true
```
