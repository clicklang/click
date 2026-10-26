# a uint32 constant above INT32_MAX prints as itself

`4000000000u` stored and read back is `4000000000u32`; a claim that it is
`1u32` is refused, and the refusal spells the value in its own type.

```c filename=a_uint32_constant_above_int32_max_prints_as_itself.c
unsigned stored(unsigned *u) {
    *u = 4000000000u;
    return *u;
}
```

```click
verifying "a_uint32_constant_above_int32_max_prints_as_itself.c";

unsigned stored(unsigned *u) {
    owns u[0..1];
    ensures result == 1u32;
}
```

```expect
fail: left side evaluated to 4000000000u32, right side evaluated to 1u32
```
