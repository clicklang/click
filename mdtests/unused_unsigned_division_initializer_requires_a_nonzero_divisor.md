# unused unsigned division initializer requires a nonzero divisor

A result that is discarded or unused does not discard the operation's domain.
The division/remainder prerequisite is checked before publishing the step.

```c filename=unused_unsigned_division_initializer_requires_a_nonzero_divisor.c
uint32 invalid(uint32 x) { uint32 unused = 1u / x; return 0; }
```

```click
verifying "unused_unsigned_division_initializer_requires_a_nonzero_divisor.c";
uint32 invalid(uint32 x) {
    requires x == 0u32;
    ensures result == 0u32;
}
```

```expect
fail: unsigned division requires a nonzero divisor
```
