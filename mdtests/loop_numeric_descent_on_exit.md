# A numeric measure can wrap on a loop exit

The proof splits the last pass from the continuing passes. When `x` reaches
4, the next test is false. The wrapping measure decreases on the continuing
passes, and the last pass owes no descent.

```c filename=loop_numeric_descent_on_exit.c
int32 fill(uint32 x) {
    while (x < 4u) {
        x++;
    }
    return 0;
}
```

```click
verifying "loop_numeric_descent_on_exit.c";

int32 fill(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases to_integer(3u32 - x);
        initialize by { solve(); }
        preserve by {
            if x == 3u32 {
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
