# Reject unsafe negation int min

```c filename=unsafe.c
int32 f(int32 x) { return -x; }
```

```click
verifying "unsafe.c";
int32 f(int32 x) {
    requires x == -2147483647 - 1;
    ensures 0 == 0;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
