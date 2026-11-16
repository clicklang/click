# Alignment closes by an explicit `rules` arithmetic certificate

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=aligned_explicit_arithmetic.c
int32 aligned_explicit_arithmetic(uint8* p) {
    return 0;
}
```

```click
verifying "aligned_explicit_arithmetic.c";

int32 aligned_explicit_arithmetic(uint8* p) {
    requires aligned(p, 16);
    ensures aligned(p + 24, 8);
} by {
    step_until(function.exit);
    have aligned(p + 24, 8) by {
        solve() using { aligned(p, 16); };
    }
    solve();
}
```

```expect
pass
```
