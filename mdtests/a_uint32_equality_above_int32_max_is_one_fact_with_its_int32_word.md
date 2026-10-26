# a uint32 equality above INT32_MAX is one fact with its int32 word

A 32-bit equality is the same fact whichever signedness it is filed at:
word equality does not depend on sign (rule K6, `design/machine-integers.md`).
An equality of `unsigned` values is filed at `uint32`, so it keeps its
operands' type in what Click prints (`u == 4294967295u32`), and it is still
the fact an `int` reading of the same word asks for: `(int)u == -1` follows
from `u == 4294967295u32`, as does the C equality `u == 4294967295u`.

```c filename=a_uint32_equality_above_int32_max_is_one_fact_with_its_int32_word.c
int is_max(unsigned u) { return u == 4294967295u; }

int signed_view(unsigned u) {
    int s = (int)u;
    return s == -1;
}

unsigned stated(unsigned u) { return u; }
```

```click
verifying "a_uint32_equality_above_int32_max_is_one_fact_with_its_int32_word.c";

int is_max(unsigned u) {
    requires u == 4294967295u32;
    ensures result == 1;
} by { execute(); simp(); }

int signed_view(unsigned u) {
    requires u == 4294967295u32;
    ensures result == 1;
} by { execute(); simp(); }

unsigned stated(unsigned u) {
    requires u == 4294967295u32;
    ensures result == 4294967295u32;
} by { execute(); simp(); }
```

```expect
pass
```
