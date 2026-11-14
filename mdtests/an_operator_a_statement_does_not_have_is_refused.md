# An operator a statement does not have is refused

`statement(0)` has one `&&` whose right operand calls a function, and no `||`,
so `statement(0).or(0)` names nothing; the refusal says what the statement has.

```c filename=no_or.c
int a(int x);
int b(int x);
int h(int x) {
    int y = a(x) && b(x);
    return y;
}
```

```click
verifying "no_or.c";
extern int32 a(int32 x) { ensures result == x; }
extern int32 b(int32 x) { ensures result == x; }
int32 h(int32 x) { requires x == 3; ensures result == 1; } by {
    step(); step();
    branch {
        step(); step();
        have statement(0).or(0).result == 1;
    } else {
        step();
    }
    step(); step();
}
```

```expect
fail: has 0 `||` operator(s) whose operands run as steps, so it has no `or(0)`
```
