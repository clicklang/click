# A positive native value may narrow to a negative signed word

```c filename=uint64_constant_lower_bound_narrowing_requires_bound.c
unsigned long identity(unsigned long mid) { return mid; }
```

```click
verifying "uint64_constant_lower_bound_narrowing_requires_bound.c";
uint64 identity(uint64 mid) {
    requires mid == 2147483648u64;
    requires 0u64 < mid;
    ensures result == mid;
} by {
    have 0 < (int32)(uint32)mid by { simp() using { 0u64 < mid; } }
    execute(); simp();
}
```

```expect
fail: could not prove
```
