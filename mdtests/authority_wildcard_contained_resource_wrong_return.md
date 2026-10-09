# Consumption cannot return a different contained resource

```c filename=contained_bad.c
void issue(int32* pool, int32* p) { }
```

```click
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
authorized resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
verifying "contained_bad.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces cell(pool, p + 1);
} by { unfold(slot(pool, p)); execute(); simp(); }
```

```expect
fail: Requires produces cell(pool, (p + 1))
```
