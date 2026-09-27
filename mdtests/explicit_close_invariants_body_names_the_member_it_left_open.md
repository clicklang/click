# an explicit `close_invariants by` body names the member it left open

The body proves the invariant and the ranking's nonnegativity, but its last
arm only restates `0 <= n` and never proves the decrease, so the bundle's
decrease member stays open. The refusal names that member, as the smart
`close_invariants()` path names the member its planner stopped at; an
explicit body used to report only that some obligation stayed open.

```c filename=explicit_close_invariants_body_names_the_member_it_left_open.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "explicit_close_invariants_body_names_the_member_it_left_open.c";

int32 drain(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and {
                    both { arithmetic() using { 0 <= n; } }
                    and { have 0 <= n by { arithmetic() using { 0 <= n; } } }
                }
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: closure body did not prove every invariant obligation: `n < at(statement(1).entry, n)` remained open
```
