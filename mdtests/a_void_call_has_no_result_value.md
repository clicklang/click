# A void call has no result value

```c filename=void_call.c
void ping(void);
void f(void) { ping(); }
```

```click
extern void ping() { ensures true; }
verifying "void_call.c";
void f() { ensures true; } by {
    step();
    have statement(0).result == 0;
    step_until(function.exit);
}
```

```expect
fail: no recorded non-void result
```
