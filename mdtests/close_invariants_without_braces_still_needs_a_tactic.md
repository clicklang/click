# `close_invariants by` without braces still needs a tactic

The brace-less body is one tactic call. Anything else after `by` is
refused where it is written, with the two spellings that are accepted.

```c filename=close_invariants_without_braces_still_needs_a_tactic.c
int32 wait_for_zero(int32 x) {
    while (x != 0) {
    }
    return 1;
}
```

```click
verifying "close_invariants_without_braces_still_needs_a_tactic.c";

int32 wait_for_zero(int32 x) diverges {
    ensures result == 1;
} by {
    loop diverges {
        invariant x == x;
        initialize by simp;
        preserve by {
            step();
            close_invariants by 3;
        }
    }
    step();
    simp();
}
```

```expect
fail: expected a proof after `close_invariants by`, got number `3`
```
