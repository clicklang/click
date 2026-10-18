# `cases` in a loop body rejoins

In a loop's `preserve` proof the arms of `cases` rejoin where they end, as a
straight-line proof `if` does there, and the proof continues once with the
facts every arm proved.

```c filename=cases_in_a_loop_body_rejoins.c
int32 count_once(int32 flag) {
    int32 i;
    i = 0;
    while (i < 1) { i = i + 1; }
    return i;
}
```

```click
verifying "cases_in_a_loop_body_rejoins.c";

int32 count_once(int32 flag) {
    ensures result == 1;
} by {
    step();
    step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        invariant i <= 1;
        initialize by simp();
        preserve by {
            step();
            have i == 0 or i == 1;
            cases {
                i == 0 => { have i <= 1; }
                i == 1 => { have i <= 1; }
            }
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
