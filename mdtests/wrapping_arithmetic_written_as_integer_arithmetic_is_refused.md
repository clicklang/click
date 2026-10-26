# Wrapping arithmetic written as Integer arithmetic is refused

Under Integer specification arithmetic the product and sum below are exact Integers, so
the claim says the C step never wraps, which is false for large `state`. It is
refused; the `click::integer` wrapping functions state the C result
(`wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`).

```c filename=wrapping_arithmetic_written_as_integer_arithmetic_is_refused.c
unsigned long step(unsigned long state, unsigned long inc) {
    return state * 6364136223846793005UL + inc;
}
```

```click

verifying "wrapping_arithmetic_written_as_integer_arithmetic_is_refused.c";

uint64 step(uint64 state, uint64 inc) {
    ensures result == state * 6364136223846793005u64 + inc;
}
```

```expect
fail: ensures to_integer(result)
```
