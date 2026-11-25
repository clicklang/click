# A C outcome cannot invent conditional evidence

```c filename=missing_condition.c
int32 identity(int32 x) { return x; }
```

```click
verifying "missing_condition.c";

int32 identity(int32 x) {
    requires x == 0;
    ensures (if x == 1 { result } else { 7 }) == result;
} by {
    step();
    close() using { x == 1; };
}
```

```expect
fail: The current goal could not be proved from only the listed premises
```
