# A selected cast still needs both range bounds


```c filename=arithmetic.c
int32 guarded(float x) { return x <= 10.0f ? (int32)x : 0; }
```

```click
verifying "arithmetic.c";

int32 guarded(float x) { ensures true; }
```

```expect
fail: explicit prerequisite proof
```
