# Listed arithmetic combines a symbolic difference bound

```c filename=symbolic_difference.c
int32 f(int32 a, int32 b) { return 0; }
```

```click
verifying "symbolic_difference.c";
int32 f(int32 a, int32 b) {
    requires b >= 1;
    requires b <= 1000;
    requires a >= 0;
    requires a <= 1000 - b;
    ensures result == 0;
} by {
    have a <= 999 by {
        arithmetic() using { a <= 1000 - b; b >= 1; b <= 1000; }
    }
    step();
    simp();
}
```

```expect
pass
```
