# A wide viewable range does not initialize its elements

A pure `viewable` premise establishes address validity, not initialized
contents. Even a bounded element inside that range needs independent
initialization evidence before `defined(bytes[k])` can be proved.

```c filename=wide_viewable_element.c
uint64 f(uint8 bytes[], uint64 n) {
    uint64 x;
    x = 0;
    return x;
}
```

```click
verifying "wide_viewable_element.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires n < 18446744073709551615u64;
    requires viewable(bytes[0..n + 1u64]);
    ensures result == 0u64 by {
        step_until(region(1));
        have forall (k: uint64) { to_integer(k) < to_integer(n + 1u64) implies defined(bytes[k]) } by {
            intro();
            intro();
            solve() using {
                to_integer(k) < to_integer(n + 1u64);
                at(function.entry, viewable(bytes[0..n + 1u64]));
            };
        }
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
