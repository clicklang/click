# An ORed literal keeps C divisors nonzero

```c filename=divide.c
uint32 divide(uint32 n, uint32 d) { return n / (d | 1u); }
uint64 remainder(uint64 n, uint64 d) { return n % (0x8000000000000000ULL | d); }
```

```click
verifying "divide.c";

uint32 divide(uint32 n, uint32 d) {
    ensures true;
} by {
    step() by { close(); }
    close();
}

uint64 remainder(uint64 n, uint64 d) {
    ensures true;
} by {
    step() by { close(); }
    close();
}

theorem observed_divisor(d: uint32) {
    ensures to_integer(d | 1u32) != 0 by { close(); }
}
```

```expect
pass
```
