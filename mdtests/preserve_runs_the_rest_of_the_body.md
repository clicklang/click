# A `preserve` that stops early runs the rest of the body

A preservation script need not step every statement to the back edge. When a
path's tactics run out inside the body, the rest of the body runs as an
omitted `preserve` runs a whole one: straight-line statements are stepped, a
C `if` with more of the body after it whose arms both fall through is run and
joined, and any other `if` splits into separate paths. Each path that reaches
the body's end, a `continue` or a `break` closes its back edge as a written
one does.

`scan` breaks at 3, continues at 5, and otherwise falls to the body's end. The
proof closes the `break` arm itself and stops one step into the other, before
the second C `if`; the rest of that path runs to the `continue` and to the
body's end, and both close `i >= 0`.

A rest that does not run is reported at the frontier the script reached
([`loop_preserve_frontier_report.md`](loop_preserve_frontier_report.md)).

```c filename=scan.c
int32 scan(int32 n) {
    int32 i = n;

    while (i > 0) {
        if (i == 3) {
            break;
        }
        if (i == 5) {
            i = i - 1;
            continue;
        }
        i = i - 1;
    }
    return i;
}
```

```click
verifying "scan.c";

int32 scan(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;

        initialize by simp;
        preserve by {
            if i == 3 {
                step();
                step();
            } else {
                step();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
