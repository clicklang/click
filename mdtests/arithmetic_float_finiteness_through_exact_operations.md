# Float negation and exact widening preserve finiteness

```c filename=arithmetic.c
int32 negated(float x) { return (int32)((-x) * 0.0f); }
int32 widened(float x) { return (int32)((double)x * 0.0); }
```

```click
verifying "arithmetic.c";

int32 negated(float x) { requires isfinite(x); ensures true; }
int32 widened(float x) { requires isfinite(x); ensures true; }

theorem negation(x: float) {
    requires isfinite(x);
    ensures isfinite(-x) by { close(); }
}

theorem widening(x: float) {
    requires isfinite(x);
    ensures isfinite(x as double) by { close(); }
}
```

```expect
pass
```
