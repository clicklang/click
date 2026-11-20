# A scalar-local literal initializer can run again in a while condition

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    int i = 0;
    while ((struct pair){i,22}.left < 2) { i++; }
    return i;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 2; } by {
    step(); step(); step();
    loop {
        decreases 2 - i;
        invariant 0 <= i and i <= 2;
        maintain by {
            step(); step();
            if i < 2 {
                step();
                have -2147483648 <= to_integer(i) + 1 by { solve(); }
                have to_integer(i) + 1 <= 2147483647 by { solve(); }
                have to_integer(i + 1) == to_integer(i) + 1 by {
                    normalize() using {
                        -2147483648 <= to_integer(i) + 1;
                        to_integer(i) + 1 <= 2147483647;
                    };
                }
                have 0 <= to_integer(i + 1) and to_integer(i + 1) <= 2 by { solve(); }
                have 0 <= 2 - to_integer(i + 1) by { solve(); }
                have 2 - to_integer(i + 1) < 2 - to_integer(i) by { solve(); }
                step();
            } else {
                step();
            }
        }
    }
}
```

```expect
pass
```
