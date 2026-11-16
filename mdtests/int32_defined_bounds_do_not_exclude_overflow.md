# `int32_defined` refuses bounds that leave room for overflow

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=int32_defined_bounds_do_not_exclude_overflow.c
int sum(int a, int b) {
    return a + b;
}
```

```click
verifying "int32_defined_bounds_do_not_exclude_overflow.c";

int32 sum(int32 a, int32 b) {
    requires 0 <= a;
    requires 0 <= b;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        solve() using { 0 <= a; 0 <= b; };
    }
}
```

```expect
fail: solve
```
