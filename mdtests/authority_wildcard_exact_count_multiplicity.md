# Equal empty members retain their multiplicity

```c filename=exact_count_multiplicity.c
void lifecycle() { int32 pool = 0; }
```

```click
authorized resource slot(pool: int32*, key: int32) {}
verifying "exact_count_multiplicity.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, 7));
    fold(slot(&pool, 7));
    fold(slot(&pool, 8));
    have count(slot(&pool, 7)) == 2;
    have count(slot(&pool, 8)) == 1;
    have count(slot(&pool, _)) == 3;
    unfold(slot(&pool, 7));
    have count(slot(&pool, 7)) == 1;
    have count(slot(&pool, 8)) == 1;
    unfold(slot(&pool, 7));
    unfold(slot(&pool, 8));
    unfold(authority(slot(&pool, _)));
    have count(slot(&pool, 7)) == 0;
    execute(); simp();
}
```

```expect
pass
```
