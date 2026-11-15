# A function-level call past the function's calls is refused

`f` calls `twice` once, so `call(twice, 1)` names nothing; the refusal says
how many times the function calls it.

```c filename=one_call.c
int32 twice(int32 x);
int32 f(int32 a) {
    int32 b = twice(a) + 1;
    return b;
}
```

```click
extern int32 twice(int32 x) {
    requires defined(x + x);
    ensures result == x + x;
}
verifying "one_call.c";
int32 f(int32 a) {
    requires a >= 0 and a <= 100;
    ensures result == 2 * a + 1;
} by {
    step(); step();
    have call(twice, 1).result == a + a;
}
```

```expect
fail: this function calls `twice` 1 time(s), so it has no `call(twice, 1)`
```
