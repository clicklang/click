# Compound literal type identity

```c filename=example.c
struct pair { int left; int right; }; int answer(void) { return __builtin_types_compatible_p(typeof((struct pair){20, 22}), struct pair); }
```

```click
verifying "example.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
