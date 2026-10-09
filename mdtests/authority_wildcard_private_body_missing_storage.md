# A private body requires actual separable memory ownership

Scalar locals alone do not provide owned memory ranges that a slot can package.

```c filename=wildcard_private_body.c
int32 lifecycle() {
    int32 pool = 0;
    int32 first = 1;
    int32 second = 2;
    first = 7;
    return first + second;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_private_body.c";
int32 lifecycle() { ensures result == 9; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, &first));
    fold(slot(&pool, &second));
    have count(slot(&pool, _)) == 2 by simp;
    open(slot(&pool, &first)) { step(); }
    have count(slot(&pool, _)) == 2 by simp;
    unfold(slot(&pool, &first));
    unfold(slot(&pool, &second));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
fail: Requires the private body of slot(p)
```
