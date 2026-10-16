# A machine difference that can wrap is not its Integer difference

Without a lower bound on `x`, the unsigned `x - 1u` wraps to `4294967295`
when `x` is `0`, so it is not the Integer `x - 1`, and `auto` does not prove
that it is (`mdtests/auto_proves_an_in_range_machine_sum_is_its_integer_sum.md`
adds the bound).

```c filename=a_machine_difference_that_can_wrap_is_not_its_integer_difference.c
unsigned decrement(unsigned x) { return x - 1u; }
```

```click
arithmetic "integer";
verifying "a_machine_difference_that_can_wrap_is_not_its_integer_difference.c";

uint32 decrement(uint32 x) {
    ensures result == x - 1;
}
```

```expect
fail: decrement
```
