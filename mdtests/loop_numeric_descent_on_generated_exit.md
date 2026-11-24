# A numeric measure can wrap on a loop exit

The next test is false when `x` reaches 4. A wrapping subtraction still
supplies the measure for continuing edges, but the last pass owes no descent.

```c filename=loop_numeric_descent_on_generated_exit.c
int32 fill(uint32 x) {
    while (x < 4u) {
        x = 4u;
    }
    return 0;
}
```

```click
verifying "loop_numeric_descent_on_generated_exit.c";

int32 fill(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases to_integer(3u32 - x);
        initialize by { close(); }
    }
}
```

```expect
pass
```
