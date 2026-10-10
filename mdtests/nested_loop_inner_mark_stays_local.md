# An inner preservation mark does not escape to its enclosing proof

```c filename=r.c
int count(void) {
    int i = 0;
    while (i < 3) {
        int j = 0;
        while (j < 2) {
            j = j + 1;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "r.c";
int32 count() {
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        preserve by {
            mark outer_head;
            have at(outer_head, i) < 3 by { simp(); }
            execute_until(loop(1));
            loop {
                decreases 2 - j;
                invariant j >= 0 and j <= 2;
                invariant i >= 0 and i <= 3;
                preserve by {
                    mark inner_head;
                    have at(outer_head, i) < 3 by { assumption(); }
                    execute_until(back_edge());
                    close_invariants();
                }
            }
            have at(inner_head, j) <= 2 by { simp(); }
            execute_until(back_edge());
            close_invariants();
        }
    }
    execute(); simp();
}
```

```expect
fail: unknown proof mark `inner_head`
```
