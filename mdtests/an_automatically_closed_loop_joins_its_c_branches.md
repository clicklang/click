# An automatically closed loop joins the arms of its C `if`s

The body has three C `if`s in a row and then the increment. Each `if` stores
to `found` when its guard holds and does nothing otherwise, so both arms fall
through to the next statement. With no written `preserve` proof, the loop
closer runs both arms of each `if`, joins them where they meet, and walks the
rest of the body once.

It does not walk the rest once per arm. That made a body of `n` such `if`s
cost `2^n` paths, and `click expand` wrote every one of them out.

The join keeps what both arms agree on. Here that is everything the
invariant needs: no arm touches `i`.

```c filename=an_automatically_closed_loop_joins_its_c_branches.c
int32 scan(int32* a, int32 n) {
    int32 i;
    int32 found;
    i = 0;
    found = 0;
    while (i < n) {
        if (a[0] == 7) {
            found = 1;
        }
        if (a[1] == 7) {
            found = 2;
        }
        if (a[2] == 7) {
            found = 3;
        }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "an_automatically_closed_loop_joins_its_c_branches.c";

int32 scan(int32* a, int32 n) {
    views a[0..3];
    requires 0 <= n;
    requires n <= 3;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
