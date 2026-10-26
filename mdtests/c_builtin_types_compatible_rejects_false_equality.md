# Same-sized incompatible types cannot establish a false equality

```c filename=incompatible.c
int32 run() { return __builtin_types_compatible_p(long, long long); }
```

```click
verifying "incompatible.c";
int32 run() { ensures result == 1 by { step_until(function.exit); normalize(); } }
```

```expect
fail: normalize
```
