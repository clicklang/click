# Reject unsafe division by zero

```c filename=unsafe.c
int32 f(int32 x, int32 y) { return x / y; }
```

```click
verifying "unsafe.c";
int32 f(int32 x, int32 y) {
    requires y == 0; requires x != -2147483647 - 1;
    ensures 0 == 0;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: division by zero
```
