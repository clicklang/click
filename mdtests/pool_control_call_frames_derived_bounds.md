# A pool control call frames bounds derived inside an open scope

Inside an open pool control the caller derives `0 <= pool->used` from a
positive requirement with the standard `int32_positive_is_nonnegative` axiom,
and restates the no-overflow fact for `used + count(slot(pool))` that the
control's sum fact implies. The following call to a reader that owns the same
control must carry those signed comparison and add-overflow condition facts
to the statement exit by frame transport. A separate pure theorem bounds the
free-slot count with an integer arithmetic certificate whose steps add
negated `to_integer` terms. This catches condition transport that drops the
overflow arm, and certificate lowering that mishandles negated conversions.

```c filename=pool_control_call_frames.c
struct pool { int32 used; int32 capacity; };
int32 pool_used(struct pool* pool) { return pool->used; }
int32 forward(struct pool* pool) { return pool_used(pool); }
```

```click
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    fact pool->capacity == pool->used + count(slot(pool));
}
theorem spare_slot_bound(capacity: int32, used: int32, slots: int32) {
    requires to_integer(capacity) == to_integer(used) + to_integer(slots);
    requires to_integer(capacity) <= 2147483647;
    requires 1 <= to_integer(used);
    ensures to_integer(slots) + 1 <= 2147483647 by {
        arithmetic_certificate {
        premise 0: to_integer(capacity) == to_integer(used) + to_integer(slots) => to_integer(capacity) == to_integer(used) + to_integer(slots);
        scale 0 by -1 => -to_integer(capacity) == -to_integer(used) - to_integer(slots);
        eq_to_le 1 => -to_integer(capacity) <= -to_integer(used) - to_integer(slots);
        premise 1: to_integer(capacity) <= 2147483647 => to_integer(capacity) <= 2147483647;
        add 2, 3 => -to_integer(capacity) + to_integer(capacity) <= -to_integer(used) - to_integer(slots) + 2147483647;
        premise 2: 1 <= to_integer(used) => 1 <= to_integer(used);
        add 4, 5 => -to_integer(capacity) + to_integer(capacity) + 1 <= -to_integer(used) - to_integer(slots) + 2147483647 + to_integer(used);
        conclusion 6;
        }
    }
}
verifying "pool_control_call_frames.c";
int32 pool_used(struct pool* pool) {
    owns control(pool);
} by {
    open(control(pool)) { execute(); }
    simp();
}
int32 forward(struct pool* pool) {
    owns control(pool);
    requires 1 <= pool->used;
    ensures defined(pool->used + count(slot(pool)));
} by {
    open(control(pool)) {
        have 0 <= pool->used by {
            apply(int32_positive_is_nonnegative(pool->used)) using { 1 <= pool->used; }
            assumption();
        }
        have defined(pool->used + count(slot(pool))) by { assumption(); }
    }
    execute(); simp();
}
```

```expect
pass
```
