# A nonzero word times an even factor can wrap to zero

```c filename=arithmetic.c
uint32 divide(uint32 n, uint32 x) { return n / (x * 2u); }
```

```click
verifying "arithmetic.c";

uint32 divide(uint32 n, uint32 x) {
    requires x != 0u32;
    ensures true by {
        have x * 2u32 != 0u32 by { close(); }
        step();
    }
}
```

```expect
fail: unsigned division requires a nonzero divisor
```
