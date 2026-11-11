# Reject unsafe negation wrong exclusion

```c filename=unsafe.c
int32 f(int32 x) { return -x; }
```

```click
verifying "unsafe.c";
int32 f(int32 x) {
    requires x != -1;
    ensures 0 == 0;
}
```

```expect
fail: requires proof excluding signed overflow
```
