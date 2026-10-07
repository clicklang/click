# Equal empty members retain their multiplicity

```c filename=exact_count_multiplicity.c
void lifecycle() { int32 pool = 0; }
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, key: int32) {}
verifying "exact_count_multiplicity.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, 7));
    fold(slot(&pool, 7));
    fold(slot(&pool, 8));
    have count(slot(&pool, 7)) == 2 by simp;
    have count(slot(&pool, 8)) == 1 by simp;
    have count(slot(&pool, _)) == 3 by simp;
    unfold(slot(&pool, 7));
    have count(slot(&pool, 7)) == 1 by simp;
    have count(slot(&pool, 8)) == 1 by simp;
    unfold(slot(&pool, 7));
    unfold(slot(&pool, 8));
    unfold(authority(slot(&pool, _)));
    have count(slot(&pool, 7)) == 0 by simp;
    execute(); simp();
}
```

```expect
pass
```
