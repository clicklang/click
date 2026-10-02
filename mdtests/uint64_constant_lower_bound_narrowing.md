# Bounded native-width comparison with a constant has a narrowing certificate

An explicit full-width upper bound is required before interpreting the low
word as a nonnegative signed index. The constant endpoint retains its value.

```c filename=uint64_constant_lower_bound_narrowing.c
unsigned long identity(unsigned long mid) { return mid; }
```

```click
verifying "uint64_constant_lower_bound_narrowing.c";
uint64 identity(uint64 mid) {
    requires 0u64 < mid;
    requires mid <= 2147483647u64;
    ensures result == mid;
} by {
    have 0 < (int32)(uint32)mid by {
        simp() using { 0u64 < mid; mid <= 2147483647u64; }
    }
    execute(); simp();
}
```

```expect
pass
```
