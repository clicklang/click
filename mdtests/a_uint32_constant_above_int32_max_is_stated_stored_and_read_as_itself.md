# a uint32 constant above INT32_MAX is stated, stored and read as itself

A `uint32` constant carries the `uint32` format (`Bitvector32Term::UInt32Constant`)
on a value at rest, so `4294967295u` is that number, not `-1`. It is stated
in a contract, stored in a cell, read back, and returned; the refusal beside
it (`a_uint32_constant_above_int32_max_prints_as_itself.md`) prints it.

```c filename=a_uint32_constant_above_int32_max_is_stated_stored_and_read_as_itself.c
unsigned literal(void) { return 4294967295u; }

unsigned stored(unsigned *u) {
    *u = 4000000000u;
    return *u;
}

unsigned stated(unsigned *u) { return *u; }

int above(unsigned *u) { return *u > 2147483647u; }
```

```click
verifying "a_uint32_constant_above_int32_max_is_stated_stored_and_read_as_itself.c";

unsigned literal() { ensures result == 4294967295u32 by auto(); }

unsigned stored(unsigned *u) {
    owns u[0..1];
    ensures result == 4000000000u32;
    ensures u[0] == 4000000000u32;
} by { execute(); simp(); }

unsigned stated(unsigned *u) {
    views u[0..1];
    requires u[0] == 4000000000u32;
    ensures result == 4000000000u32;
} by { execute(); simp(); }

int above(unsigned *u) {
    views u[0..1];
    requires u[0] == 4000000000u32;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
