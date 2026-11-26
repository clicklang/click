# A cursor advanced by a full-width stride keeps its offset

A loop moves `v` forward by `cs` bytes while `vl` counts down, as
Rust's `ChunksExact::next` does. Each pass regroups `(b + k) + 4u64` as
`b + (k + 4u64)` from the bound on `k + 4u64`.

```c filename=lp.c
unsigned long lp(const unsigned char *b, unsigned long n) {
    unsigned long cs = 4;
    unsigned long rl = n % cs;
    const unsigned char *v = b;
    unsigned long vl = n - rl;
    while (cs <= vl) {
        v = v + cs;
        vl = vl - cs;
    }
    return rl;
}
```

```click
verifying "lp.c";
uint64 lp(const uint8* b, uint64 n) {
    views b[0u64..n];
    ensures result == n % 4u64;
} by {
    step_until(loop(0).entry);
    loop {
        decreases vl;
        views b[0u64..n];
        invariant rl == n % 4u64;
        invariant cs == 4u64;
        invariant vl <= n - n % 4u64;
        invariant v == b + (n - n % 4u64 - vl);
        initialize by {
            have n % 4u64 <= n;
            close();
        }
        maintain by {
            if 4u64 <= vl {
                have n % 4u64 <= n;
                have to_integer((n - n % 4u64 - vl) + 4u64) <= to_integer(n);
                have to_integer(n - n % 4u64 - vl) + 4 <= to_integer(n);
                have to_integer(n - n % 4u64 - vl) < to_integer(n);
                mark head;
                step_until(loop(0).back_edge);
                have v == at(head, v) + 4u64;
                have vl == at(head, vl) - 4u64;
                have 4u64 <= at(head, vl) by close();
                apply(click::integer::uint64_subtract_to_integer(at(head, vl), 4u64));
                have to_integer(vl) == to_integer(at(head, vl)) - 4 by close();
                have to_integer(vl) < to_integer(at(head, vl)) by {
                    rewrite(to_integer(vl), to_integer(at(head, vl)) - 4);
                    close();
                }
                have vl < at(head, vl) by { close(); }
                have at(head, v) == b + (n - n % 4u64 - at(head, vl));
                have to_integer(n - n % 4u64 - at(head, vl)) + 4 <= 18446744073709551615;
                have (b + (n - n % 4u64 - at(head, vl))) + 4u64 == b + ((n - n % 4u64 - at(head, vl)) + 4u64);
                have (n - n % 4u64 - at(head, vl)) + 4u64 == n - n % 4u64 - vl;
                have v == b + (n - n % 4u64 - vl);
                have vl <= n - n % 4u64 by {
                    close() using { vl < at(head, vl); at(head, vl) <= n - n % 4u64; };
                }
                have 0 <= to_integer(vl);
                close();
            } else {
                step();
            }
        }
    }
    step_until(function.exit);
}
```

```expect
pass
```
