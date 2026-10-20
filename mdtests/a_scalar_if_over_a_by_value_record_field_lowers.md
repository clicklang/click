# A scalar `if` over a by-value record's fields lowers

A postcondition whose value is a scalar `if` reads a field of the by-value
record parameter in its condition and in a branch. Its arms are `uint32` and
`uint8` values, not `int`, and the `else` arm is the `int` literal `0`, which
C's usual arithmetic conversions make `unsigned int` beside a `uint32` arm.
Lowering it used to drop the conditional and produce no path.

```c filename=a_scalar_if_over_a_by_value_record_field_lowers.c
struct pair {
    uint8 flag;
    uint32 value;
};

uint32 pick(struct pair p) {
    if (p.flag != 0) {
        return p.value;
    }
    return 0;
}

uint8 flag_or_one(struct pair p) {
    if (p.flag != 0) {
        return p.flag;
    }
    return 1;
}
```

```click
verifying "a_scalar_if_over_a_by_value_record_field_lowers.c";

uint32 pick(struct pair p) {
    ensures result == (if p.flag != 0 { p.value } else { 0 });
} by {
    execute();
    simp();
}

uint8 flag_or_one(struct pair p) {
    ensures result == (if p.flag != 0 { p.flag } else { (uint8)1 });
} by {
    execute();
    simp();
}
```

```expect
pass
```
