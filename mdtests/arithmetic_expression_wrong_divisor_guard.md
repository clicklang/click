# A guard that selects zero does not establish a nonzero divisor

```c filename=arithmetic.c
uint32 guarded(uint32 n, uint32 d) { return d == 0u ? n / d : 0u; }
```

```click
verifying "arithmetic.c";

uint32 guarded(uint32 n, uint32 d) { ensures true; }
```

```expect
fail: division by zero
```
