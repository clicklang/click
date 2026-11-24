# Signed addition and multiplication retain their ternary guards

```c filename=arithmetic.c
int32 sum(int32 x, int32 y) {
    return (x >= 0 && y >= 0 && x <= 2147483647 - y) ? x + y : 0;
}
int32 product(int32 x, int32 y) {
    return (x >= 0 && y > 0 && x <= 2147483647 / y) ? x * y : 0;
}
int32 signalled(int32 x, int32 y) {
    return (x >= 0 && y >= 0 && x <= 2147483647 - y) ? 1 : 0;
}
```

```click
verifying "arithmetic.c";

int32 sum(int32 x, int32 y) { ensures true; }
int32 product(int32 x, int32 y) { ensures true; }

int32 signalled(int32 x, int32 y) {
    requires x >= 0;
    requires y >= 0;
    requires to_integer(x) > 2147483647 - to_integer(y);
    ensures result == 0;
}
```

```expect
pass
```
