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
    have 0 < mid as uint32 as int32 by { solve() using { 0u64 < mid; }; }
}
```

```expect
fail: could not prove
```
