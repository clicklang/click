# Valid counts and bounded operands can still overflow

```c filename=arithmetic.c
int32 shift(int32 x, int32 k) { return x << k; }
```

```click
verifying "arithmetic.c";

int32 shift(int32 x, int32 k) {
    requires x >= 0;
    requires x <= 3;
    requires k >= 0;
    requires k <= 30;
    ensures true;
}
```

```expect
fail: signed overflow
```
