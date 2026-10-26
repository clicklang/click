# Statement regions count an `if`'s arms together

`statement(i).statement(j)` is the `j`th statement `statement(i)` controls.
An `if`'s arms share one count in source order, so here the then-arm holds
`statement(1).statement(0)` and `statement(1).statement(1)`, and the else-arm
starts at `statement(1).statement(2)`. A loop's statements are reached either
through the statement the loop is or as `loop(i).statement(j)`: in
[`statement_regions_reach_a_loop_body.md`](statement_regions_reach_a_loop_body.md),
`loop(0).statement(0)` and `statement(2).statement(0)` are one point.

```c filename=statement_paths_if.c
int32 f(int32 v) { return v + 1; }
int32 probe(int32 x) {
    int32 y = x;
    if (y > 0) {
        y = f(y);
        y = y + 1;
    } else {
        y = 0;
    }
    return y;
}
```

```click
verifying "statement_paths_if.c";

int32 f(int32 v) {
    requires v < 1000;
    ensures result == v + 1;
}

int32 probe(int32 x) {
    requires x < 10;
    ensures result >= 0;
} by {
    step();
    if x > 0 {
        step(); step(); step();
        have at(statement(1).statement(0).call(f, 0).entry, y) == x by solve();
        have at(statement(1).statement(0).exit, y) == x + 1 by solve();
        have at(statement(1).statement(1).entry, y) == x + 1 by solve();
        step_until(function.exit); solve();
    } else {
        step_until(function.exit); solve();
    }
}
```

```expect
pass
```
