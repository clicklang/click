# `solve` proves a `size_t`-bounded viewable range from a constant 32-bit one

`viewable(bytes[0..3])` and `viewable(bytes[0..n])` with `n == 3u64` name the same
bytes, so the wide range follows from the stated 32-bit one.

```c filename=solve_proves_wide_viewable_from_a_constant_32_bit_range.c
uint64 f(uint8 bytes[], uint64 n) {
    return 0;
}
```

```click
verifying "solve_proves_wide_viewable_from_a_constant_32_bit_range.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires viewable(bytes[0..3]);
    requires n == 3u64;

    ensures result == 0u64 by {
        have viewable(bytes[0..n]) by {
            solve();
        }
        have viewable(bytes[0..3u64]) by {
            solve();
        }
    }
}
```

```expect
pass
```
