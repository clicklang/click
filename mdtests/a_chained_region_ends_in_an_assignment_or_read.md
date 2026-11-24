# A chained region ends in an assignment or a read

`.assignment(x, j)` and `.read(j)` end a chained region, as `.call(f, j)`
does: each counts, from zero, the statement's own atomic regions that assign
local `x` or load from memory. `step_until` stops before that region, and
`at` reads its states. Here `statement(2).statement(1).read(0)` is the load
`x = (int32)*p;` inside the `if`, and `statement(2).statement(2).assignment(y,
0)` is the store `y = 2;` after it.

```c filename=chained_kinds.c
int32 loaded(const uint8* p) {
    int32 x = 0;
    int32 y = 0;
    if (x == 0) {
        y = 1;
        x = (int32)*p;
        y = 2;
    }
    return x + y;
}
```

```click
verifying "chained_kinds.c";
int32 loaded(const uint8* p) {
    views p[0..1];
    ensures 2 <= result and result <= 257;
} by {
    step_until(statement(2).statement(1).read(0).entry);
    step();
    have 0 <= x and x <= 255;
    step_until(statement(2).statement(2).assignment(y, 0).entry);
    have at(statement(2).statement(1).read(0).entry, y) == 1 by close();
    step();
    have y == 2 by close();
    have 0 <= to_integer(x) by close();
    have to_integer(x) <= 255 by close();
    have to_integer(x) <= to_integer(2147483647 - 2) by {
        apply(click::integer::le_transitive(to_integer(x), 255, to_integer(2147483647 - 2)));
    }
    apply(click::integer::int32_nonnegative_add_within_max_is_defined(x, 2));
    apply(click::integer::int32_add_to_integer(x, 2));
    have 2 <= to_integer(x) + 2 by {
        rewrite(2, 0 + 2);
        apply(click::integer::add_right_order(0, to_integer(x), 2));
    }
    have to_integer(x) + 2 <= 257 by {
        rewrite(257, 255 + 2);
        apply(click::integer::add_right_order(to_integer(x), 255, 2));
    }
    step();
    have to_integer(result) == to_integer(old(p[0])) + 2 by close();
    have 2 <= result by close();
    have result <= 257 by close();
}
```

```expect
pass
```
