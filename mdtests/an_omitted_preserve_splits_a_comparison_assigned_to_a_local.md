# An omitted `preserve` splits a comparison assigned to a local

A comparison whose value is stored, `_Bool odd = (i % 2 == 1);`, has two
successors that only its condition tells apart. The implicit tail splits the
proof on that condition and steps each case. An omitted `preserve` walks the body
the same way, so the stored comparison and the `if` that reads it need no
written body. Rust lowers every `if` condition to such a stored `bool`.

```c filename=evens.c
int32 count_evens(int32 n) {
    int32 i = 0;
    int32 evens = 0;
    while (i < n) {
        i += 1;
        _Bool odd = (i % 2 == 1);
        if (odd) {
            continue;
        }
        evens += 1;
    }
    return evens;
}
```

```click
verifying "evens.c";

int32 count_evens(int32 n) {
    requires n >= 0;
    ensures 0 <= result and result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n and 0 <= evens and evens <= i;
    }
}
```

```expect
pass
```
