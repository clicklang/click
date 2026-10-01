# Birth cannot also return the child transferred into its body

```c filename=contained_bad.c
void issue(int32* pool, int32* p) { }
```

```click resource_semantics=authority
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
verifying "contained_bad.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes cell(pool, p);
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
    produces cell(pool, p);
} by { fold(slot(pool, p)); execute(); simp(); }
```

```expect
fail: Requires produces cell(pool, p)
```
