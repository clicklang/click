# The ternary must actually rule out signed overflow

```c filename=arithmetic.c
int32 product(int32 x, int32 y) {
    return (x >= 0 && y > 0) ? x * y : 0;
}
```

```click
verifying "arithmetic.c";

int32 product(int32 x, int32 y) {
    requires x >= 0;
    requires y > 0;
    ensures true;
}
```

```expect
fail: signed overflow
```
