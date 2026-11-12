# unsigned remainder requires a nonzero divisor

A result that is discarded or unused does not discard the operation's domain.
The division/remainder prerequisite is checked before publishing the step.

```c filename=unsigned_remainder_requires_a_nonzero_divisor.c
uint32 invalid(uint32 x) { return 1u % x; }
```

```click
verifying "unsigned_remainder_requires_a_nonzero_divisor.c";
uint32 invalid(uint32 x) {
    requires x == 0u32;
    ensures result == 0u32;
}
```

```expect
fail: unsigned division requires a nonzero divisor
```
