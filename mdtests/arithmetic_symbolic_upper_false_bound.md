# Listed arithmetic rejects a false tighter symbolic bound

```c filename=symbolic_false_bound.c
int32 f(int32 a, int32 b) { return 0; }
```

```click
verifying "symbolic_false_bound.c";
int32 f(int32 a, int32 b) {
    requires b >= 1;
    requires b <= 1000;
    requires a >= 0;
    requires a <= 1000 - b;
    ensures result == 0;
} by {
    have a <= 998 by {
        arithmetic() using { a <= 1000 - b; a >= 0; b >= 1; b <= 1000; }
    }
    step();
    simp();
}
```

```expect
fail: exactly the listed premises were insufficient
```
