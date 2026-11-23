# Short-circuit and conditional operands keep the conditions for evaluating them

```c filename=arithmetic.c
uint32 guarded_and(uint32 n, uint32 d) { return d != 0u && (n / d) != 0u; }
uint32 guarded_ternary(uint32 n, uint32 d) { return (d & 7u) != 0u ? n / (d & 7u) : 0u; }
int32 cast_and(float x) { return (x >= -10.0f && x <= 10.0f) && (int32)x != 0; }
int32 cast_or(float x) { return !(x >= -10.0f && x <= 10.0f) || (int32)x != 0; }
```

```click
verifying "arithmetic.c";

uint32 guarded_and(uint32 n, uint32 d) { ensures true; }
uint32 guarded_ternary(uint32 n, uint32 d) { ensures true; }
int32 cast_and(float x) { ensures true; }
int32 cast_or(float x) { ensures true; }
```

```expect
pass
```
