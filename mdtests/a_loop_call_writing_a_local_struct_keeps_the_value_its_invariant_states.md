# A loop's call writing a local struct keeps the struct's value as its invariant states

`run` only views its parameter, and each loop pass hands `&c` to `bump`,
which increments `c.n`. The invariant `c.n == i` carries the struct's value
across the loop, so `run` returns 3. The refusal of a false result is
`a_loop_call_writing_a_local_struct_forgets_its_earlier_value.md`.

```c filename=loop_call_writes_local.c
struct counter { int32 n; };
void bump(struct counter *c);
int32 run(const int32 *p) {
    struct counter c;
    int32 i;
    c.n = 0;
    i = 0;
    while (i < 3) {
        bump(&c);
        i = i + 1;
    }
    return c.n;
}
```

```click
verifying "loop_call_writes_local.c";

extern void bump(struct counter *c) {
    owns c[0..1];
    requires c->n < 100;
    ensures c->n == old(c->n) + 1;
}

int32 run(const int32 *p) {
    views p[0..1];
    ensures result == 3;
} by {
    step_until(loop(0));
    have c.n == 0;
    loop {
        decreases 3 - i;
        invariant 0 <= i and i <= 3;
        invariant c.n == i;
    }
}
```

```expect
pass
```
