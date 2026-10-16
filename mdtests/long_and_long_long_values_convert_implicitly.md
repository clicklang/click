# `long` and `long long` values convert implicitly

`long` and `long long` are distinct types, but integer values convert between
them silently at initialization, assignment, argument passing, and return, as
between any arithmetic types (C11 6.5.16.1p1), and both have the same 64-bit
range on x86-64 Linux, so no conversion changes a value. Mixed arithmetic
takes the common type of greater rank, `long long` (C11 6.3.1.8), and
`unsigned long` with `long long` gives `unsigned long long`. Only pointers to
them stay apart; see
`a_long_pointer_does_not_initialize_a_long_long_pointer.md`.

```c filename=main.c
long narrow(long long value) {
    long x = value;
    return x;
}

long round_trip(long value) {
    long x = (long long)value;
    long long y = 0;
    y = x;
    return y;
}

long long sum(long a, long long b) {
    return a + b;
}

unsigned long long mixed(unsigned long a, long long b) {
    return a + b;
}

long long take(long long value) {
    return value;
}

long pass_long(long value) {
    return take(value);
}

long long read_both(long *a, long long *b) {
    return *a + *b;
}
```

```click
verifying "main.c";

long narrow(long long value) {
    ensures result == value by auto();
}

long round_trip(long value) {
    ensures result == value by auto();
}

long long sum(long a, long long b) {
    requires a >= 0 and a <= 100;
    requires b >= 0 and b <= 100;
    ensures result == a + b by auto();
}

unsigned long long mixed(unsigned long a, long long b) {
    requires a <= 100u64;
    requires b == 7;
    ensures result == a + 7u64 by auto();
}

long long take(long long value) {
    ensures result == value by auto();
}

long pass_long(long value) {
    ensures result == value;
} by {
    execute();
    simp();
}

long long read_both(long *a, long long *b) {
    views a[0];
    views b[0];
    requires a[0] >= 0 and a[0] <= 100;
    requires b[0] >= 0 and b[0] <= 100;
    ensures result == a[0] + b[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
