# A folded control supplies a symbolic resource quantity

Entry setup may read a field owned by an explicitly required folded control.
The control and its authority remain folded. Both clause orders must work;
this checks symbolic quantities at entry, not symbolic batch helper transfer.

```c filename=quantity.c
struct pool { int32 checked_out; int32 capacity; };
void inspect(struct pool* pool) {}
void reversed(struct pool* pool) {}
```

```click
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}
verifying "quantity.c";
void inspect(struct pool* pool) {
    owns control(pool);
    owns pool->capacity of slot(pool);
    ensures 0 <= pool->capacity;
} by {
    execute(); simp();
}
void reversed(struct pool* pool) {
    owns pool->capacity of slot(pool);
    owns control(pool);
    ensures 0 <= pool->capacity;
} by {
    execute(); simp();
}
```

```expect
pass
```
