# A known zero divisor makes unsigned remainder undefined

```c filename=remainder.c
uint64 remainder(uint64 x, uint64 y) { return x % y; }
```

```click
verifying "remainder.c";

uint64 remainder(uint64 x, uint64 y) {
    requires y < 1u64;
    ensures true;
}
```

```expect
fail: undefined behavior: division by zero
```
