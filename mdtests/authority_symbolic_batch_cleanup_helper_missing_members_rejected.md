# A cleanup call cannot borrow the global total in place of members

This reduced single-population fixture checks call effects independently of
bounded-pool cleanup's additional empty population. The caller has no slots
although the control authenticates a nonzero count.

```c filename=cleanup.c
struct pool { int32 capacity; };
void cleanup(struct pool* pool) { pool->capacity = 0; }
void forward(struct pool* pool) { cleanup(pool); }
void nested(struct pool* pool) { forward(pool); }
void empty(struct pool* pool) { cleanup(pool); }
```

```click
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    fact 0 <= pool->capacity;
    fact pool->capacity == count(slot(pool));
}
verifying "cleanup.c";
void cleanup(struct pool* pool) {
    consumes control(pool);
    consumes pool->capacity of slot(pool);
    produces *pool;
    ensures pool->capacity == 0;
    ensures count(slot(pool)) == 0;
} by {
    unfold(control(pool));
    unfold(pool->capacity of slot(pool));
    have count(slot(pool)) == 0 by simp;
    step();
    unfold(authority(slot(pool)));
    execute(); simp();
}
void forward(struct pool* pool) {
    consumes control(pool);
    consumes pool->capacity of slot(pool);
    produces *pool;
    ensures pool->capacity == 0;
    ensures count(slot(pool)) == 0;
} by {
    execute(); simp();
}
void nested(struct pool* pool) {
    consumes control(pool);
    consumes pool->capacity of slot(pool);
    produces *pool;
    ensures pool->capacity == 0;
    ensures count(slot(pool)) == 0;
} by {
    execute(); simp();
}
void empty(struct pool* pool) {
    consumes control(pool);
    consumes 0 of slot(pool);
    requires pool->capacity == 1;
    produces *pool;
    ensures pool->capacity == 0;
    ensures count(slot(pool)) == 0;
} by { execute(); simp(); }
```

```expect
fail: population call transfer refused: MissingMembers
```
