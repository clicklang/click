# Omitted array compound literal elements have the zero of their element type

```c filename=example.c
int answer(void) {
    short *numbers = (short[4]){42};
    double *samples = (double[2]){1.0};
    return numbers[0] + numbers[3] + (samples[1] == 0.0 ? 0 : 1);
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
