# An integer cast can use the conditions of its selected arm


```c filename=arithmetic.c
int32 guarded(float x) { return x >= -10.0f && x <= 10.0f ? (int32)x : 0; }
```

```click
verifying "arithmetic.c";

int32 guarded(float x) { ensures true; }
```

```expect
pass
```
