# Pointer association at a full-width unsigned index

`(b + d) + 4u64` and `b + (d + 4u64)` are one address when the `uint64`
sum `d + 4u64` does not wrap. The bound that says so,
`to_integer(d) + 4 <= 18446744073709551615`, is the one fact the
regrouping reads.

```c filename=assoc.c
int assoc(const unsigned char *b, unsigned long n, unsigned long d) { return 0; }
```

```click
verifying "assoc.c";
int32 assoc(const uint8* b, uint64 n, uint64 d) {
    requires 4u64 <= n;
    requires n <= 2000u64;
    requires d <= n - 4u64;
    views b[0u64..n];
    ensures result == 0;
} by {
    have to_integer(d) + 4 <= to_integer(n);
    have to_integer(d) + 4 <= 18446744073709551615;
    have (b + d) + 4u64 == b + (d + 4u64) by {
        solve() using { to_integer(d) + 4 <= 18446744073709551615; };
    }
    have (b + d) + 4u64 == b + (d + 4u64);
    step_until(function.exit);
}
```

```expect
pass
```
