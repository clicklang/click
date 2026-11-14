# A loop condition's call and test are the loop's own regions

`while (take(&left))` calls `take` and tests its result on every pass. The
call and the test are the loop's own atomic regions, between its head and its
body: the pass steps the call, then the test, whose false side leaves the loop
there. No statement of the source is invented for them.

After the loop, the points of the pass that left are named as they were
inside it: `statement(2).call(take, 0).entry` is that pass's call, its
`.result` what the call returned, and `loop(0).test()` the test that found it
false. The proof states the case the facts there decide, that `take` found
`left` empty, and the rest closes.

```c filename=take_loop.c
int take(int *n) {
    if (*n == 0) return 0;
    *n = *n - 1;
    return 1;
}
unsigned count(int n) {
    int left = n;
    unsigned c = 0;
    while (take(&left)) {
        c = c + 1;
    }
    return c;
}
```

```click
verifying "take_loop.c";
int take(int *n) {
    requires *n >= 0;
    owns n[0..1];
    ensures result == (if old(*n) == 0 { 0 } else { 1 });
    ensures *n == (if old(*n) == 0 { 0 } else { old(*n) - 1 });
}
unsigned count(int n) {
    requires n >= 0;
    ensures to_integer(result) == to_integer(n);
} by {
    step_until(loop(0));
    loop {
        decreases to_integer(n) - to_integer(c);
        invariant left >= 0;
        invariant to_integer(c) + to_integer(left) == to_integer(n);
        preserve by {
            step();
            have statement(2).call(take, 0).result
                == (if at(statement(2).call(take, 0).entry, left) == 0 { 0 } else { 1 }) by solve();
            have left
                == (if at(statement(2).call(take, 0).entry, left) == 0 { 0 }
                    else { at(statement(2).call(take, 0).entry, left) - 1 }) by solve();
            if statement(2).call(take, 0).result != 0 {
                have at(statement(2).call(take, 0).entry, left) != 0 by {
                    if at(statement(2).call(take, 0).entry, left) == 0 {
                        have statement(2).call(take, 0).result == 0 by solve();
                        contradiction(statement(2).call(take, 0).result == 0);
                    } else {
                        solve();
                    }
                }
                have left == at(statement(2).call(take, 0).entry, left) - 1 by solve();
            } else {
            }
        }
    }
    have at(statement(2).call(take, 0).entry, left) == 0 by {
        if at(statement(2).call(take, 0).entry, left) == 0 {
            solve();
        } else {
            have statement(2).call(take, 0).result == 1 by solve();
            have statement(2).call(take, 0).result != 1 by solve();
            contradiction(statement(2).call(take, 0).result == 1);
        }
    }
    have at(loop(0).test().entry, left) == 0 by solve();
}
```

```expect
pass
```
