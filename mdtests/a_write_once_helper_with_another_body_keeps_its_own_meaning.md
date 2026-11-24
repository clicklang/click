# A `WRITE_ONCE` helper with another body keeps its own meaning

`WRITE_ONCE(x, value)` spelled `__WRITE_ONCE(x, value)` is the sequential
store only while `__WRITE_ONCE` has the recognized body where it is used.
Here the helper stores `value + 1`, so `WRITE_ONCE` expands to it and the
claim that it stores `value` fails.

```c filename=main.c
#define __WRITE_ONCE(x, value) x = (typeof(x))((value) + 1)
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)

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
