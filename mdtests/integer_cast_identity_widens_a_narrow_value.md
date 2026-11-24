# `integer_cast_identity` widens a narrow value

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=widen_cert.c
int widen8(signed char x) { return x; }
long widen8l(signed char x) { return x; }
unsigned int widenu8(unsigned char x) { return x; }
unsigned long widenu16(unsigned short x) { return x; }
```

```click
verifying "widen_cert.c";

int widen8(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    close() using { old(x) as int32 >= -128; old(x) as int32 <= 127; };
}

long widen8l(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    close() using { old(x) as int32 >= -128; old(x) as int32 <= 127; };
}

unsigned int widenu8(unsigned char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    close() using { old(x) as int32 >= 0; old(x) as int32 <= 255; };
}

unsigned long widenu16(unsigned short x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    close() using { old(x) as int32 >= 0; old(x) as int32 <= 65535; };
}
```

```expect
pass
```
