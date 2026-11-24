# A `WRITE_ONCE` macro with another body keeps its own meaning

Click reads `WRITE_ONCE` as a sequential store only through a recognized
definition. A macro with that name and a different body is expanded as
written. This one stores `value + 1`, so the claim that it stores `value`
fails.

```c filename=main.c
#define WRITE_ONCE(x, value) x = (typeof(x))((value) + 1)

void store(int32 *p, int32 v) {
    WRITE_ONCE(*p, v);
}
```

```click
verifying "main.c";

void store(int32 *p, int32 v) {
    requires v < 100 and v > 0;
    owns *p;
    ensures *p == v;
}
```

```expect
fail: unclosed goal
```
