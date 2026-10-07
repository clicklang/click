# Unsigned reduction preserves a small dividend

The native strict bound excludes zero divisors and retains full-width unsigned
values. Adler32 byte lanes satisfy this bound before reduction by 65521.

```c filename=test.c
unsigned int reduce_lane(unsigned int value) { return value % 65521u; }
```

```click
verifying "test.c";
theorem byte_lane(value: uint32) {
    requires value <= 255u32;
    ensures value % 65521u32 == value by {
        have value < 65521u32 by { arithmetic() using { value <= 255u32; } }
        apply(uint32_remainder_of_lt(value, 65521u32));
    }
    ensures to_integer(value % 65521u32) == to_integer(value) by {
        have value < 65521u32 by { arithmetic() using { value <= 255u32; } }
        apply(uint32_remainder_of_lt(value, 65521u32));
        rewrite(value % 65521u32 == value);
        simp() using {};
    }
}
theorem full_width(value: uint32) {
    requires value < 4294967295u32;
    ensures value % 4294967295u32 == value by {
        apply(uint32_remainder_of_lt(value, 4294967295u32));
    }
}
uint32 reduce_lane(uint32 value) {
    requires value <= 255u32;
    ensures result == value;
} by {
    execute();
    apply(byte_lane(value));
    simp();
}
```

```expect
pass
```
