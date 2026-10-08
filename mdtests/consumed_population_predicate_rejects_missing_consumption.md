# consumed population predicates require the actual consumption

Declaring consumption does not perform it. Updating concrete capacity without
consuming the matching members cannot restore the private accounting invariant.

```c filename=consume_population.c
struct owner {
    int32 used;
    int32 capacity;
};

void consume_population(struct owner* owner, int32 amount) {
    owner->capacity = owner->capacity - amount;
}
```

```click
authorized resource slot(owner: struct owner*) {
}

authorized abstract resource item(owner: struct owner*, id: int32);

resource accounting(owner: struct owner*) {
    owns owner->used;
    owns owner->capacity;
    owns authority(slot(owner));
    owns authority(item(owner, _));
    fact 0 <= owner->used;
    fact owner->used == count(item(owner, _));
    fact owner->capacity == owner->used + count(slot(owner));
}

predicate valid_capacity(owner: struct owner*) {
    0 <= owner->used and
    owner->used == count(item(owner, _)) and
    owner->capacity == owner->used + count(slot(owner))
}

verifying "consume_population.c";

void consume_population(struct owner* owner, int32 amount) {
    requires valid_capacity(owner);
    requires 0 <= amount;
    requires amount <= count(slot(owner));
    requires defined(owner->capacity - amount);
    owns accounting(owner);
    consumes amount of slot(owner);

    ensures valid_capacity(owner);
} by {
    open(accounting(owner)) {
        unfold(valid_capacity);
        step();
    }
    execute();
    unfold(valid_capacity);
    simp();
}
```

```expect
fail: Requires owner->capacity == (owner->used + count(slot(owner)))
```
