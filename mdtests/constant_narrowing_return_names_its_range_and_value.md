# Constant narrowing at an return names its failing bound

```c filename=constant_narrowing_return_names_its_range_and_value.c
unsigned char f(void) { int x = -56; return x; }
```

```click
verifying "constant_narrowing_return_names_its_range_and_value.c";
uint8 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
fail: uint8 narrowing lower bound: the facts refute `-56 >= 0`
```
