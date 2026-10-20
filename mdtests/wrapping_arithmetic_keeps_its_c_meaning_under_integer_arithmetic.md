# Wrapping arithmetic keeps its C meaning under Integer arithmetic

Under `arithmetic "integer";` a specification's `+`, `-` and `*` compare exact
Integers, so they cannot state the result of C arithmetic that wraps. The
`machine_integer` wrapping functions are the C operations themselves: a
comparison between machine values with no Integer arithmetic keeps its C
meaning, so a linear congruential step that relies on `uint64` wraparound is
stated and verified as written. The same claim with `*` and `+` is refused
(`wrapping_arithmetic_written_as_integer_arithmetic_is_refused.md`).

```c filename=wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.c
unsigned long step(unsigned long state, unsigned long inc) {
    return state * 6364136223846793005UL + inc;
}

unsigned int down(unsigned int value) {
    return value - 1u;
}
```

```click
arithmetic "integer";

import click::machine_integer;

verifying "wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.c";

uint64 step(uint64 state, uint64 inc) {
    ensures result == uint64_wrapping_add(
        uint64_wrapping_mul(state, 6364136223846793005u64),
        inc
    );
} by auto();

uint32 down(uint32 value) {
    ensures result == uint32_wrapping_sub(value, 1u32);
} by auto();
```

```expect
pass
```
