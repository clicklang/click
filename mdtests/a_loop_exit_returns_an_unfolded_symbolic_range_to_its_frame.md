# a loop exit returns an unfolded symbolic range to its frame

A loop owns a resource holding `p[0..n]`, unfolds it, stores to `p[0]` and
breaks. At the exit the unfolded range, whose end is symbolic, is exchanged
back into the enclosing frame. Its endpoints are not both concrete, so the
exchange checks it against the frame's other owned ranges one by one rather
than through the concrete same-base neighbours. This catches a loop-exit
exchange that refuses, or skips the validity check of, a symbolic range.

```c filename=a_loop_exit_returns_an_unfolded_symbolic_range_to_its_frame.c
void fill(int32 *p, int32 n) {
    while (true) {
        p[0] = 1;
        break;
    }
}
```

```click
verifying "a_loop_exit_returns_an_unfolded_symbolic_range_to_its_frame.c";

resource cell(p: int32*, n: int32) {
    owns p[0..n];
}

void fill(int32 *p, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes cell(p, n);
    ensures 1 == 1;
} by {
    execute_until(loop(0));
    loop {
        owns cell(p, n);
        decreases 0;
        initialize by simp;
        preserve by {
            unfold(cell(p, n));
            step();
            step();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
