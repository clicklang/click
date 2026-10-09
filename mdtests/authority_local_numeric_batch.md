# A local numeric batch supports partial consumption

```c filename=local_batch.c
int32 run() { int32 pool = 0; return 0; }
```

```click
authorized resource token(pool: int32*) {}
verifying "local_batch.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(token(&pool)));
    fold(0 of token(&pool));
    unfold(0 of token(&pool));
    fold(3 of token(&pool));
    have count(token(&pool)) == 3;
    unfold(token(&pool));
    have count(token(&pool)) == 2;
    unfold(2 of token(&pool));
    have count(token(&pool)) == 0;
    unfold(authority(token(&pool)));
    execute(); simp();
}
```

```expect
pass
```
