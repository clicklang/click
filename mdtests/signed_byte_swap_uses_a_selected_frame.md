# Signed byte swap uses a selected frame

The stated index disequality keeps the cached first cell available across
the second store, including through the matching signed-byte conversions.

```c filename=swap.c
void swap(int8* p, uint64 n) {
    int8 t = p[0];
    p[0] = p[n - 1];
    p[n - 1] = t;
}
```
```click
verifying "swap.c";
void swap(int8* p, uint64 n) {
    owns p[0u64..n];
    requires 2u64 <= n;
    requires n <= 1000u64;
    ensures p[0] == old(p[n - 1]);
} by {
    have ((n - 1u64) as uint64) != 0u64 by close();
    step_until(function.exit);
    have p[0] == old(p[n - 1]) by {
        close();
    }
}
```
```expect
pass
```
