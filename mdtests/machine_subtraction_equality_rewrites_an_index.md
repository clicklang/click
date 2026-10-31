# A mathematical subtraction equality rewrites a machine index

```c filename=rw.c
unsigned int pick(unsigned int *xs, unsigned long n, unsigned long r) {
    return xs[n - 1];
}
```

```click
verifying "rw.c";

uint32 pick(uint32* xs, uint64 n, uint64 r) {
    requires r == 0u64 and n != 0u64;
    views xs[0..n];
    ensures result == xs[(n - r) - 1u64];
} by {
    have n - 1u64 == (n - r) - 1u64 by {
        rewrite(r == 0u64);
        solve();
    }
    have xs[n - 1u64] == xs[(n - r) - 1u64] by {
        rewrite(n - 1u64 == (n - r) - 1u64);
        solve();
    }
}
```

```expect
pass
```
