# An unsigned branch in an Integer comparison does not wrap

A branch of an `if` in an Integer comparison is an Integer position, so
`u + 1` there is `to_integer(u) + 1`. At `u == 4294967295u32` it is the exact
4294967296, not the wrapped 0 of C's `uint32` sum, and the claim that it
exceeds `u - 1` holds in both branches.

```c filename=an_unsigned_branch_in_an_integer_comparison_does_not_wrap.c
uint32 keep_unsigned(uint32 u, int32 c) {
    return u;
}
```

```click
verifying "an_unsigned_branch_in_an_integer_comparison_does_not_wrap.c";

uint32 keep_unsigned(uint32 u, int32 c) {
    requires u == 4294967295u32;
    ensures (if c > 0 { u + 1 } else { u }) > result - 1 by {
        step_until(function.exit);
        if c > 0 {
            have (if c > 0 { u + 1 } else { u }) == u + 1 by simp();
            simp();
        } else {
            have (if c > 0 { u + 1 } else { u }) == u by simp();
            simp();
        }
    }
}
```

```expect
pass
```
