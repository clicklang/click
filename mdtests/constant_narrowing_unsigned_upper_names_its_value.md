# A constant narrowing upper bound preserves its source value

```c filename=constant_narrowing_unsigned_upper_names_its_value.c
int f(void) { unsigned int x = 300; unsigned char y = x; return y; }
```

```click
verifying "constant_narrowing_unsigned_upper_names_its_value.c";
int32 f() { ensures result == 44; } by { execute(); simp(); }
```

```expect
fail: uint8 narrowing upper bound): the facts refute `300u64 <= 255u64`
```
