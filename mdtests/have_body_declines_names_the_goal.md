# A failing `have` reports its written operation

The checked driver runs the source body once. Its first `close()` reports
the failure to prove `n + 1 > 500` and identifies the operation's position in
the body.

```c filename=have_body_declines_names_the_goal.c
int spin(int n) {
    return n;
}
```

```click
verifying "have_body_declines_names_the_goal.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    have n + 1 > 500 by {
        close();
        close();
    }
}
```

```expect
fail: have body tactic 1: `solve` failed for `spin.contract`: could not establish `(to_integer(n) + 1) > 500`
```
