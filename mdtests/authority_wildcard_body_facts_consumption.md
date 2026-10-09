# Consuming an exact member exposes its private invariant

```c filename=wildcard_body_facts_consumption.c
int32 take(int32* pool, int32* p) { return p[0]; }
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; fact 0 <= p[0]; }
verifying "wildcard_body_facts_consumption.c";
int32 take(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces p[0..1];
    ensures 0 <= result;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by { unfold(slot(pool, p)); execute(); simp(); }
```

```expect
pass
```
