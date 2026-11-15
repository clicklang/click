# A call is named among the function's calls

`call(f, j)` on its own names the function's `j`th call of `f`, counting its
calls in the order they run, and `call(j)` its `j`th call of any function.
Here `twice` is called twice, in two statements: `call(twice, 1)` is the
second, in `statement(1)`, the same call `statement(1).call(twice, 0)` names.

```c filename=function_calls.c
int32 twice(int32 x);
int32 f(int32 a) {
    int32 b = twice(a) + 1;
    int32 c = twice(b) + 1;
    return c;
}
```

```click
extern int32 twice(int32 x) {
    requires defined(x + x);
    ensures result == x + x;
}
verifying "function_calls.c";
int32 f(int32 a) {
    requires a >= 0 and a <= 100;
    ensures result == 4 * a + 3;
} by {
    step_until(statement(2));
    have call(twice, 1).result == statement(1).call(twice, 0).result;
    have call(twice, 0).result == a + a;
    have call(1).result == call(twice, 1).result;
}
```

```expect
pass
```
