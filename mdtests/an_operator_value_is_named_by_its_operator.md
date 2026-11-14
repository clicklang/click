# An operator's value is named by its operator

`a(x) && b(x)` calls `b` only when `a`'s result is nonzero, so the `&&` decides
between its operands as a step of the statement: `statement(0).and(0)`. On
each path its value is that path's result, `statement(0).and(0).result`; no
local holds it.

```c filename=and_value.c
int a(int x);
int b(int x);
int h(int x) {
    int y = a(x) && b(x);
    return y;
}
```

```click
verifying "and_value.c";
extern int32 a(int32 x) { ensures result == x; }
extern int32 b(int32 x) { ensures result == x; }
int32 h(int32 x) { requires x == 3; ensures result == 1; } by {
    step(); step();
    branch {
        step(); step();
        have statement(0).and(0).result == 1;
    } else {
        step();
    }
    step(); step();
}
```

```expect
pass
```
