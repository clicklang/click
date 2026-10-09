# Nested helpers exchange two resource families

The caller keeps another capacity slot and another checked-out object. A
helper consumes one slot and packages supplied object ownership into a member.

```c filename=family_exchange.c
struct payload { int32 value; };
void checkout(int32* pool, struct payload* p) {}
void forward(int32* pool, struct payload* p) { checkout(pool, p); }
int32 lifecycle(struct payload* first, struct payload* second) {
    int32 pool = 0;
    first->value = 1;
    second->value = 2;
    forward(&pool, first);
    int32 result = first->value + second->value;
    return result;
}
```

```click
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
void forward(int32* pool, struct payload* p) {
    owns authority(capacity(pool));
    owns authority(item(pool, _));
    consumes capacity(pool);
    consumes *p;
    requires defined(count(item(pool, _)) + 1);
    produces item(pool, p);
    ensures p->value == old(p->value);
    ensures count(capacity(pool)) == old(count(capacity(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
} by { execute(); simp(); }
int32 lifecycle(struct payload* first, struct payload* second) {
    owns *first;
    owns *second;
    ensures result == 3;
} by {
    step(); step(); step(); step();
    fold(authority(capacity(&pool)));
    fold(authority(item(&pool, _)));
    fold(capacity(&pool));
    fold(capacity(&pool));
    fold(item(&pool, second));
    step();
    have count(capacity(&pool)) == 1;
    have count(item(&pool, _)) == 2;
    open(item(&pool, first)) { open(item(&pool, second)) { step(); step(); } }
    unfold(capacity(&pool));
    unfold(item(&pool, first));
    unfold(item(&pool, second));
    unfold(authority(capacity(&pool)));
    unfold(authority(item(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
