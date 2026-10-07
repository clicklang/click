# Reject unsafe division unbounded

```c filename=unsafe.c
int32 f(int32 x, int32 y) { return x / y; }
```

```click
verifying "unsafe.c";
int32 f(int32 x, int32 y) {
    requires y != 0;
    ensures 0 == 0;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
