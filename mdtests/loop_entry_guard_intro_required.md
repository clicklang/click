# Deleting a loop-entry guard introduction is rejected

The quantified entry claim requires introduction of the quantifier before
`close() using {}` can act on its body.

```c filename=loop_entry_guard_intro_required.c
int32 loop_entry_guard_intro_required(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "loop_entry_guard_intro_required.c";

int32 loop_entry_guard_intro_required(int32 p[3]) {
    consumes p[0..3];
    ensures returns_third: result == 2;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };

        initialize by {
            have i >= 0 and i <= 3 by {
                all {
                    i >= 0 => {
                        close();
                    }
                    i <= 3 => {
                        close();
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < i implies p[k] == k } by {
                close() using {};
            }
        }
        maintain by close();
    }
    step();
    close();
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
