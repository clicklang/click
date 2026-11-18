# Initializer updates remain visible to outer unsequenced operands

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    int i = 0;
    return (struct pair){i++, 22}.left + i;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 1; }
```

```expect
fail: an assignment expression and an unsequenced operand read
```
