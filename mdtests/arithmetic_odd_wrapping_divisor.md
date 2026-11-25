# An odd factor preserves nonzero in a wrapping word

```c filename=arithmetic.c
uint32 divide(uint32 n, uint32 x) { return n / (x * 3u); }
uint64 remain(uint64 n, uint64 x) { return n % (5ULL * x); }
```

```click
verifying "arithmetic.c";

uint32 divide(uint32 n, uint32 x) { requires x != 0u32; ensures true; }
uint64 remain(uint64 n, uint64 x) { requires x != 0u64; ensures true; }

theorem odd_product(x: uint32) {
    requires x != 0u32;
    ensures ((x * 3u32) as uint32) != 0u32 by {
        close() using { x != 0u32; };
    }
}
```

```expect
pass
```
