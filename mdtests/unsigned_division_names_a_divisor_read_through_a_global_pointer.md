# An unsigned divisor read through a global pointer has a Surface form

The `by` block checks the generated nonzero-divisor obligation. The
obligation needs to name the read through the global pointer as `*divisor`.

```c filename=divide.c
uint32 value = 2;
uint32 *divisor = &value;
uint32 divide() { return 6u / *divisor; }
```

```click
verifying "divide.c";
uint32 divide() {
    owns divisor[0..1];
    requires *divisor != 0u32;
    ensures true;
} by {
    step() by { known(); }
}
```

```expect
pass
```
