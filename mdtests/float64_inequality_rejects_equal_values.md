# Double inequality cannot prove that an ordinary value differs from itself

```click
theorem float64_one_differs() {
    ensures float64_from_bits(0x3ff0000000000000) != float64_from_bits(0x3ff0000000000000) by { normalize(); }
}
```

```expect
fail: goal did not normalize to true
```
