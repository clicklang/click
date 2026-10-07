# Reject unsafe negation unbounded

```c filename=unsafe.c
int32 f(int32 x) { return -x; }
```

```click
verifying "unsafe.c";
int32 f(int32 x) {

    ensures 0 == 0;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
