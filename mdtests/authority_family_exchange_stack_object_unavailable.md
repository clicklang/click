# Implicit stack storage is not transferable object ownership

This unchanged C exposes a separate ownership gap: local struct declarations
provide implicit access, not explicit transferable object facts. The helper
proof verifies, but packaging the local second object is currently refused.
This is not evidence of support for moving stack storage into a resource.

```c filename=family_exchange.c
struct payload { int32 value; };
void checkout(int32* pool, struct payload* p) {}
int32 lifecycle() {
    int32 pool = 0;
    struct payload first;
    struct payload second;
    first.value = 1;
    second.value = 2;
    checkout(&pool, &first);
    int32 result = first.value + second.value;
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
    requires count(item(pool, p)) == 0;
    produces item(pool, p);
    ensures count(capacity(pool)) == old(count(capacity(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures count(item(pool, p)) == 1;
} by {
    unfold(capacity(pool));
    fold(item(pool, p));
    execute(); simp();
}
int32 lifecycle() { ensures result == 3; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(capacity(&pool)));
    fold(authority(item(&pool, _)));
    fold(capacity(&pool));
    fold(capacity(&pool));
    fold(item(&pool, &second));
    step();
    have count(capacity(&pool)) == 1 by simp;
    have count(item(&pool, _)) == 2 by simp;
    have count(item(&pool, &first)) == 1 by simp;
    have count(item(&pool, &second)) == 1 by simp;
    open(item(&pool, &first)) { open(item(&pool, &second)) { step(); step(); } }
    unfold(capacity(&pool));
    unfold(item(&pool, &first));
    unfold(item(&pool, &second));
    unfold(authority(capacity(&pool)));
    unfold(authority(item(&pool, _)));
    execute(); simp();
}
```

```expect
fail: missing resource fact `owns second`
```
