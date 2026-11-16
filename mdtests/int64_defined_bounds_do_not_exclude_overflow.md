# `int64_defined` refuses bounds that leave room for overflow

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=int64_defined_bounds_do_not_exclude_overflow.c
long sum(long a, long b) {
    return a + b;
}
```

```click
verifying "int64_defined_bounds_do_not_exclude_overflow.c";

int64 sum(int64 a, int64 b) {
    requires a < 100;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        solve() using { a < 100; };
    }
}
```

```expect
fail: solve
```
