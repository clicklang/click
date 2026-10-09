# A member birth cannot promise an unchanged population total

```c filename=contained_bad.c
void issue(int32* pool, int32* p) { }
```

```click
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
authorized resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
verifying "contained_bad.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes cell(pool, p);
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
    ensures count(slot(pool, _)) == old(count(slot(pool, _)));
} by { execute(); simp(); }
```

```expect
fail: Requires produces slot(pool, p)
```
