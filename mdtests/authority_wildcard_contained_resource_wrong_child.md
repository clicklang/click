# An unrelated cell cannot establish the selected member

```c filename=contained_bad.c
void issue(int32* pool, int32* p) { }
```

```click resource_semantics=authority
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
verifying "contained_bad.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes cell(pool, p + 1);
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
} by { fold(slot(pool, p)); execute(); simp(); }
```

```expect
fail: missing resource fact `cell(pool, p)`
```
