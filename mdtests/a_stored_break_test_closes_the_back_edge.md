# A stored `break` test closes the back edge

A loop that stores its exit test in a local and breaks on it closes its back
edge from that test's false branch: a negated comparison, `not (a >= b)`,
which arithmetic reads as `a < b`
([`arithmetic_using_reads_a_negated_order_premise.md`](arithmetic_using_reads_a_negated_order_premise.md)).
Rust lowers `if i >= n { break; }` this way.

```c filename=stop.c
int32 first_stop(int32 n, int32 limit) {
    int32 i = 0;
    while (1) {
        if (i >= limit) {
            break;
        }
        int32 a = i;
        int32 b = n;
        _Bool stop = (a >= b);
        if (stop) {
            break;
        }
        i += 1;
    }
    return i;
}
```

```click
verifying "stop.c";

int32 first_stop(int32 n, int32 limit) {
    requires 0 <= n and 0 <= limit;
    ensures result <= n and result <= limit;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n and i <= limit;
    }
}
```

```expect
pass
```
