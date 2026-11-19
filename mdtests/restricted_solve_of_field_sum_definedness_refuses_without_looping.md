# `solve() using` on a field sum's definedness refuses instead of looping

`defined(pool->checked_out + 1)` states two things: the read of
`pool->checked_out` is defined, and the sum does not overflow. Restricted
`solve` splits the two and searches the overflow half, which has no Source
spelling of its own. Spelling it as `defined(...)` again names the whole
conjunction, so opening that `have` and searching it reached the same half
again until the stack overflowed. The search now uses a spelled `have` only
when it states the goal itself. The listed bound does not give the read's
definedness, so the step is refused promptly.

```c filename=pool.c
struct pool { int32 checked_out; int32 capacity; };
void bump(struct pool* pool) { pool->checked_out = pool->checked_out + 1; }
```

```click
verifying "pool.c";
void bump(struct pool* pool) {
    owns *pool;
    requires pool->checked_out < 2147483647;
    ensures pool->checked_out == old(pool->checked_out) + 1;
} by {
    have defined((pool->checked_out + 1)) by {
        solve() using { at(function.entry, pool->checked_out) < at(function.entry, 2147483647); };
    }
    step();
    step();
    known();
}
```

```expect
fail: `solve() using` could not prove the current goal from only its listed premises
```
