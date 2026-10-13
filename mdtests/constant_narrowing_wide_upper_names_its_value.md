# A constant narrowing upper bound preserves its source value

```c filename=constant_narrowing_wide_upper_names_its_value.c
int f(void) { long x = 4294967296L; return x; }
```

```click
verifying "constant_narrowing_wide_upper_names_its_value.c";
int32 f() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: int32 narrowing upper bound): the facts refute `4294967296i64 <= 2147483647i64`
```
