# `int64` definedness from the operands' bounds is an explicit step

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=int64_defined_from_bounds.c
long sum(long a, long b) {
    return a + b;
}

long difference(long a, long b) {
    return a - b;
}

long sum_by_solve(long a, long b) {
    return a + b;
}

long sum_by_listed_solve(long a, long b) {
    return a + b;
}

long mixed(unsigned int tag, long b) {
    return tag + b;
}
```

```click
verifying "int64_defined_from_bounds.c";

int64 sum(int64 a, int64 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        solve() using { a < 100; b == 1; };
    }
}

int64 difference(int64 a, int64 b) {
    requires -5 <= a;
    requires 0 <= b;
    requires not (b > 7);
    ensures to_integer(result) == to_integer(a - b);
} by {
    have defined(a - b) by {
        solve() using { -5 <= a; 0 <= b; not (b > 7); };
    }
}

int64 sum_by_solve(int64 a, int64 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        solve();
    }
}

int64 sum_by_listed_solve(int64 a, int64 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        solve() using {
            a < 100;
            b == 1;
        };
    }
}

int64 mixed(uint32 tag, int64 b) {
    requires b < 100;
    ensures to_integer(result) == to_integer(tag + b);
} by {
    have defined(tag + b) by {
        solve() using { b < 100; };
    }
}
```

```expect
pass
```
