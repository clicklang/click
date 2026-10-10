# A wide viewable range does not carry an element outside it

The guard `k < n + 2u64` admits `k == n + 1`, one past the viewable range
`bytes[0..n + 1u64]`, so the transport is refused.

```c filename=wide_viewable_element_outside.c
uint64 f(uint8 bytes[], uint64 n) {
    uint64 x;
    x = 0;
    return x;
}
```

```click
verifying "wide_viewable_element_outside.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires n < 18446744073709551615u64;
    requires viewable(bytes[0..n + 1u64]);
    ensures result == 0u64 by {
        execute_until(statement(1));
        have forall (k: uint64) { k < n + 2u64 implies defined(bytes[k]) } by {
            intro();
            intro();
            transport(
                at(function.entry, viewable(bytes[0..n + 1u64])),
                defined(bytes[k])
            ) using {
                k < n + 2u64;
                at(function.entry, viewable(bytes[0..n + 1u64]));
            }
        }
        execute();
        simp();
    }
}
```

```expect
fail: so the target must follow from the source and the listed premises alone
```
