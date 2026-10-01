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
resource slot(pool: int32*, member: int32*, tag: int32) {}
verifying "wildcard_lifecycle.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _, _)));
    have count(slot(&pool, _, _)) == 0 by simp;
    fold(slot(&pool, &first, 10));
    fold(slot(&pool, &second, 20));
    have count(slot(&pool, _, _)) == 2 by simp;
    unfold(slot(&pool, &first, 10));
    have count(slot(&pool, _, _)) == 1 by simp;
    unfold(slot(&pool, &second, 20));
    have count(slot(&pool, _, _)) == 0 by simp;
    unfold(authority(slot(&pool, _, _)));
    execute(); simp();
}
```

```expect
pass
```
