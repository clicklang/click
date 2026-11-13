# Unsigned division domains name their computed and read operands

The prerequisite retains the C divisor, including its wrapping word operation
or selected read. Neither case needs a generated binding or an inline search.

```c filename=divisors.c
uint32 computed_divisor(uint32 x, uint32 y) { return x / (y + 1u); }
uint32 read_divisor(uint32 *p, uint32 *q) { return p[0] / q[0]; }
```

```click
verifying "divisors.c";
uint32 computed_divisor(uint32 x, uint32 y) {
    requires ((y + 1u32) as uint32) != 0u32;
    ensures result == x / ((y + 1u32) as uint32);
} by {
    step() by { assumption(); }
    assumption();
}
uint32 read_divisor(uint32* p, uint32* q) {
    views p[0];
    views q[0];
    requires q[0] != 0u32;
    ensures result == p[0] / q[0];
} by {
    step() by { assumption(); }
    assumption();
}
```

```expect
pass
```
