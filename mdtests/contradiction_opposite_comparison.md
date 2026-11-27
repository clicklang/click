# Opposite comparisons establish false

The exact facts `x < 0` and `x >= 0` establish `false` in the introduced
branch. Its proof closes with `close()`.

```c filename=contradiction_opposite_comparison.c
int32 nonnegative_identity(int32 x) {
    return x;
}
```

```click
verifying "contradiction_opposite_comparison.c";

int32 nonnegative_identity(int32 x) {
    requires x >= 0;
    ensures result == x;
} by {
    have x < 0 implies x == 7 by {
        intro() {
            close();
        }
    }
    step();
    close();
}
```

```expect
pass
```
