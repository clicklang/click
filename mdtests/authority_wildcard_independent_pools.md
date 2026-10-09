# Independent pools keep independent aggregate totals

```c filename=independent_pools.c
void independent() {
    int32 left = 0;
    int32 right = 0;
    int32 member = 0;
}
```

```click
authorized resource slot(pool: int32*, member: int32*) {}
verifying "independent_pools.c";
void independent() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&left, _)));
    fold(authority(slot(&right, _)));
    fold(slot(&left, &member));
    fold(slot(&right, &member));
    have count(slot(&left, _)) == 1;
    have count(slot(&right, _)) == 1;
    unfold(slot(&left, &member));
    have count(slot(&left, _)) == 0;
    have count(slot(&right, _)) == 1;
    unfold(authority(slot(&left, _)));
    unfold(slot(&right, &member));
    unfold(authority(slot(&right, _)));
    execute(); simp();
}
```

```expect
pass
```
