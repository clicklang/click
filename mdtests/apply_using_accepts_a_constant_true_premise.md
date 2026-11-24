# A theorem application accepts a true constant requirement

Applying the theorem with `lo = 0` instantiates its lower-bound requirement
as `0 <= 0`, which the checker establishes directly.

```c filename=apply_using_accepts_a_constant_true_premise.c
int32 probe(int32 n) {
    return 0;
}
```

```click
verifying "apply_using_accepts_a_constant_true_premise.c";

theorem start_below(lo: int32, n: int32) {
    requires 0 <= lo;
    requires lo <= n;
    ensures 0 <= n by close();
}

int32 probe(int32 n) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    apply(start_below(0, n));
    close();
}
```

```expect
pass
```
