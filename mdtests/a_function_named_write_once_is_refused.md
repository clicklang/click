# A function named `WRITE_ONCE` is refused

The sequential access primitives come only from their recognized macro
definitions. A C function named `WRITE_ONCE` is an ordinary function, which
returns `x + y` and stores nothing, so the call is refused rather than read
as a store to `x`.

```c filename=main.c
int32 WRITE_ONCE(int32 x, int32 y) {
    return x + y;
}

int32 use(int32 x) {
    WRITE_ONCE(x, 1);
    return x;
}
```

```click
verifying "main.c";

int32 WRITE_ONCE(int32 x, int32 y) {
    requires x < 1000 and x > 0 and y < 1000 and y > 0;
    ensures result == x + y;
}

int32 use(int32 x) {
    requires x < 1000 and x > 0;
    ensures result == 1;
}
```

```expect
fail: `WRITE_ONCE` is called here without a recognized `#define WRITE_ONCE`
```
