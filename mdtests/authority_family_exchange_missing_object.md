# Checkout requires supplied object ownership

The caller keeps another capacity slot and another checked-out object. A
helper consumes one slot and packages supplied object ownership into a member.

```c filename=family_exchange.c
struct payload { int32 value; };
void checkout(int32* pool, struct payload* p) {}
void caller(int32* pool, struct payload* p) { checkout(pool, p); }
int32 lifecycle(struct payload* first, struct payload* second) {
    int32 pool = 0;
    first->value = 1;
    second->value = 2;
    checkout(&pool, first);
    int32 result = first->value + second->value;
    return result;
}
```

```click resource_semantics=authority
authorized resource capacity(pool: int32*) {}
authorized resource item(pool: int32*, p: struct payload*) { owns *p; }
verifying "family_exchange.c";
void checkout(int32* pool, struct payload* p) {
    owns authority(capacity(pool));
    owns authority(item(pool, _));
    consumes capacity(pool);
    consumes *p;
    requires defined(count(item(pool, _)) + 1);
    produces item(pool, p);
    ensures p->value == old(p->value);
    ensures count(capacity(pool)) == old(count(capacity(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
} by {
    unfold(capacity(pool));
    fold(item(pool, p));
    execute(); simp();
}
void caller(int32* pool, struct payload* p) {
    owns authority(capacity(pool));
    owns authority(item(pool, _));
    consumes capacity(pool);
    requires defined(count(item(pool, _)) + 1);
    produces item(pool, p);
    ensures p->value == old(p->value);
} by { execute(); simp(); }

```

```expect
fail: missing resource fact
```
