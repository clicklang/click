# An `int32` branch in an Integer comparison is exact

A comparison that does arithmetic reads as Integer, and each branch of an
`if` in it is in the comparison's position. So `a + 1` in a branch reads
`to_integer(a) + 1`: at `a == 2147483647` it is the exact 2147483648, with no
definedness obligation, where C's `a + 1` would overflow. The C sum is still
available when it is meant: `to_integer(if c > 0 { a + 1 } else { a })`
observes the C conditional and owes the overflow obligation of its branch.

```c filename=an_int32_branch_in_an_integer_comparison_is_exact.c
int32 keep(int32 a, int32 c) {
    return a;
}
```

```click
verifying "an_int32_branch_in_an_integer_comparison_is_exact.c";

int32 keep(int32 a, int32 c) {
    requires a == 2147483647;
    ensures (if c > 0 { a + 1 } else { a }) > result - 1 by {
        execute();
        if c > 0 {
            have (if c > 0 { a + 1 } else { a }) == a + 1 by simp();
            simp();
        } else {
            have (if c > 0 { a + 1 } else { a }) == a by simp();
            simp();
        }
    }
}
```

```expect
pass
```
