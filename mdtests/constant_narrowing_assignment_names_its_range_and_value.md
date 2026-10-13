# Constant narrowing at an assignment names its failing bound

```c filename=constant_narrowing_assignment_names_its_range_and_value.c
int f(void) { int x = -56; unsigned char c = 0; c = x; return c; }
```

```click
verifying "constant_narrowing_assignment_names_its_range_and_value.c";
int32 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
fail: uint8 narrowing lower bound): the facts refute `-56 >= 0`
```
