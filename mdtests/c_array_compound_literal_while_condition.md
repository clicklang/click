# A literal with omitted elements can be initialized again in a loop condition

```c filename=example.c
int answer(void) {
    int i = 0;
    while ((int[2]){i}[0] < 2) { i++; }
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
                have -2147483648 <= to_integer(i) + 1 by { close(); }
                have to_integer(i) + 1 <= 2147483647 by { close(); }
                have to_integer(i + 1) == to_integer(i) + 1 by {
                    close() using {
                        -2147483648 <= to_integer(i) + 1;
                        to_integer(i) + 1 <= 2147483647;
                    };
                }
                have 0 <= to_integer(i + 1) and to_integer(i + 1) <= 2 by { close(); }
                have 0 <= 2 - to_integer(i + 1) by { close(); }
                have 2 - to_integer(i + 1) < 2 - to_integer(i) by { close(); }
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
