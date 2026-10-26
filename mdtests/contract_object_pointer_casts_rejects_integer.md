# A contract void-pointer cast requires an object pointer

```c filename=integer.c
struct item { int32 value; };
int32 run(int32 x) { return x; }
```

```click
verifying "integer.c";
int32 run(int32 x) {
    views (x as (void *) as (struct item *))->value;
    ensures result == x;
} by { step_until(function.exit); normalize(); }
```

```expect
fail: expects an object pointer operand
```
