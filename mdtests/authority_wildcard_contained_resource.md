# Population members preserve contained resources

A member owns an ordinary cell resource. Its helper transfers the cell into
and out of membership, while a member-only helper opens both resource layers.
The caller retains another member, and the cell population never changes.

```c filename=wildcard_contained_resource.c
void issue(int32* pool, int32* p) { }
void update(int32* pool, int32* p) { p[0] = 7; }
void release(int32* pool, int32* p) { }
int32 lifecycle() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    issue(&pool, p);
    update(&pool, p);
    release(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
verifying "wildcard_contained_resource.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes cell(pool, p);
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) + 1;
} by { fold(slot(pool, p)); execute(); simp(); }
void update(int32* pool, int32* p) {
    owns slot(pool, p);
    ensures p[0] == 7;
} by { open(slot(pool, p)) { open(cell(pool, p)) { step(); } } execute(); simp(); }
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces cell(pool, p);
    ensures p[0] == old(p[0]);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by { unfold(slot(pool, p)); execute(); simp(); }
int32 lifecycle() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch { then { execute(); simp(); } else {} }
    step(); step();
    fold(authority(cell(&pool, _)));
    fold(cell(&pool, p));
    fold(cell(&pool, p + 1));
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, p + 1));
    step(); step(); step();
    have count(slot(&pool, _)) == 1 by simp;
    have count(cell(&pool, _)) == 2 by simp;
    open(cell(&pool, p)) {
        open(slot(&pool, p + 1)) {
            open(cell(&pool, p + 1)) { step(); step(); }
        }
    }
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
    unfold(cell(&pool, p));
    unfold(cell(&pool, p + 1));
    unfold(authority(cell(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
