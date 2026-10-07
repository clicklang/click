# Listed arithmetic combines a symbolic sum bound

```c filename=symbolic_sum.c
int32 f(int32 a, int32 b) { return 0; }
```

```click
verifying "symbolic_sum.c";
int32 f(int32 a, int32 b) {
    requires b >= 1;
    requires b <= 1000;
    requires a >= 0;
    requires a <= 1000;
    requires a + b <= 1000;
    ensures result == 0;
} by {
    have a < 1000 by {
        arithmetic() using { a + b <= 1000; a >= 0; a <= 1000; b >= 1; b <= 1000; }
    }
    step();
    simp();
}
```

```expect
pass
```
