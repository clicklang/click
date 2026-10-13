# Constant narrowing at an argument names its failing bound

```c filename=constant_narrowing_argument_names_its_range_and_value.c
int take(unsigned char c) { return c; }
int f(void) { int x = -56; return take(x); }
```

```click
verifying "constant_narrowing_argument_names_its_range_and_value.c";
int32 take(uint8 c) { ensures result == c; } by { execute(); simp(); }
int32 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
fail: uint8 narrowing lower bound): the facts refute `-56 >= 0`
```
