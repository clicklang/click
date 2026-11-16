# Full-width pointer association requires its own bound

Without `to_integer(d) + 4 <= 18446744073709551615` available,
`normalize` does not regroup `(b + d) + 4u64`.

```c filename=assoc.c
int assoc(const unsigned char *b, unsigned long n, unsigned long d) { return 0; }
```

```click
verifying "assoc.c";
int32 assoc(const uint8* b, uint64 n, uint64 d) {
    requires 4u64 <= n;
    requires d <= n - 4u64;
    views b[0u64..n];
    ensures result == 0;
} by {
    have (b + d) + 4u64 == b + (d + 4u64) by {
        normalize() using { to_integer(d) + 4 <= 18446744073709551615; };
    }
    step_until(function.exit);
}
```

```expect
fail: not exactly available
```
