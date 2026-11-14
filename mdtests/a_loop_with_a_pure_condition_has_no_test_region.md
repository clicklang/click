# A loop with a pure condition has no test region

`while (n > 0)` reads only the state at its head, so its test is decided where
each pass starts, before any region of the loop's own. `loop(0).test()` names
a loop's own test region, which this loop does not have, and is refused.

```c filename=pure_test.c
int drain(int n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "pure_test.c";
int drain(int n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
    }
    have at(loop(0).test().entry, n) == 0 by solve();
}
```

```expect
fail: tests its condition at its head, before any region of its own, so it has no `test()`
```
