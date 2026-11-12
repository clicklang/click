# discarded unsigned division requires a nonzero divisor

A result that is discarded or unused does not discard the operation's domain.
The division/remainder prerequisite is checked before publishing the step.

```c filename=discarded_unsigned_division_requires_a_nonzero_divisor.c
uint32 invalid(uint32 x) { (void)(1u / x); return 0; }
```

```click
verifying "discarded_unsigned_division_requires_a_nonzero_divisor.c";
uint32 invalid(uint32 x) {
    requires x == 0u32;
    ensures result == 0u32;
}
```

```expect
fail: unsigned division requires a nonzero divisor
```
