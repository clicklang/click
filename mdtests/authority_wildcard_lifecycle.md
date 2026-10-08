# One authority governs the members of one pool

A field-free family has a concrete storage anchor and a wildcard member
argument. Creating and consuming two different members updates the same total;
empty retirement closes the population.

```c filename=wildcard_lifecycle.c
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_lifecycle.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    have count(slot(&pool, _)) == 0;
    fold(slot(&pool, &first));
    fold(slot(&pool, &second));
    have count(slot(&pool, _)) == 2;
    unfold(slot(&pool, &first));
    have count(slot(&pool, _)) == 1;
    unfold(slot(&pool, &second));
    have count(slot(&pool, _)) == 0;
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
