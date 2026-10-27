# Recursive measures use Integer arithmetic in each component

The sum can exceed `int32`. Both a single measure and each component of a
lexicographic measure observe the machine parameters before adding them.

```c filename=recursive_measures.c
int32 scalar(int32 a, int32 b) {
    if (a > 0) {
        return scalar(a - 1, b);
    }
    return 0;
}

int32 lexicographic(int32 a, int32 b) {
    if (a > 0) {
        return lexicographic(a - 1, b);
    }
    return 0;
}
```

```click
verifying "recursive_measures.c";

int32 scalar(int32 a, int32 b) {
    decreases a + b;
    requires a >= 0;
    requires b >= 0;
    ensures result == 0;
}

int32 lexicographic(int32 a, int32 b) {
    decreases (a + b, a);
    requires a >= 0;
    requires b >= 0;
    ensures result == 0;
}
```

```expect
pass
```
