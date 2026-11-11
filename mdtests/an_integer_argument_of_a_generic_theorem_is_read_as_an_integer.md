# An Integer argument of a generic theorem is read as an Integer

A generic theorem or function may take a mathematical `Integer` beside its
typed parameters. The `Integer` parameter decides no type argument, so its
argument is not read for a C type: an unsuffixed literal is an `Integer`
there, not an `int32`, and a loop's pass count `iterations` is passed as it
is, in an `apply` a smart step runs as well as in a written one.

```c filename=count.c
unsigned long count(unsigned long n) {
    unsigned long i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count.c";

spec enum Box<T> {
    Box(T),
}

function shifted<T>(b: Box<T>, k: Integer) -> Integer {
    k + 1
}

theorem shifted_is_next<T>(b: Box<T>, k: Integer) {
    requires 0 <= k;
    ensures shifted(b, k) == k + 1 by {
        unfold(shifted(b, k));
        normalize();
    }
}

theorem at_a_literal(b: Box<uint64>) {
    ensures shifted(b, 2) == 3 by {
        apply(shifted_is_next(b, 2));
        solve();
    }
}

unsigned long count(unsigned long n) {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant to_integer(i) == iterations;
        preserve by {
            have shifted(Box<uint64>::Box(i), iterations) == iterations + 1 by {
                apply(shifted_is_next(Box<uint64>::Box(i), iterations));
            }
        }
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
