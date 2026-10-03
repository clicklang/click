# Four authenticated unit effects move an object and exchange pool slots

This reduced fixture isolates the member transfers needed by the original pool
transfer. The empty helper changes only proof ownership. A caller retains a
source object and a destination slot while a second object moves between pools.
Concrete counter updates and control restoration are a separate integration
slice against the unchanged pool C.

```c filename=four_effect_exchange.c
void move(int32* source, int32* destination, int32* p) {}
int32 lifecycle() {
    int32 source = 0;
    int32 destination = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 7;
    p[1] = 11;
    move(&source, &destination, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
resource slot(pool: int32*) {}
resource item(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "four_effect_exchange.c";
void move(int32* source, int32* destination, int32* p) {
    requires source != destination;
    owns authority(slot(source));
    owns authority(slot(destination));
    owns authority(item(source, _));
    owns authority(item(destination, _));
    consumes item(source, p);
    consumes slot(destination);
    requires defined(count(slot(source)) + 1);
    requires defined(count(item(destination, _)) + 1);
    produces item(destination, p);
    produces slot(source);
    ensures p[0] == old(p[0]);
    ensures count(item(source, _)) == old(count(item(source, _))) - 1;
    ensures count(item(destination, _)) == old(count(item(destination, _))) + 1;
    ensures count(slot(source)) == old(count(slot(source))) + 1;
    ensures count(slot(destination)) == old(count(slot(destination))) - 1;
} by {
    unfold(item(source, p));
    unfold(slot(destination));
    fold(item(destination, p));
    fold(slot(source));
    execute(); simp();
}
int32 lifecycle() { ensures result == 0 or result == 18; } by {
    step(); step(); step(); step(); step(); step();
    branch then { execute(); simp(); } else {}
    step(); step();
    fold(authority(slot(&source)));
    fold(authority(slot(&destination)));
    fold(authority(item(&source, _)));
    fold(authority(item(&destination, _)));
    fold(slot(&destination)); fold(slot(&destination));
    fold(item(&source, p)); fold(item(&source, p + 1));
    step();
    have count(item(&source, _)) == 1 by simp;
    have count(item(&destination, _)) == 1 by simp;
    have count(slot(&source)) == 1 by simp;
    have count(slot(&destination)) == 1 by simp;
    open(item(&destination, p)) { open(item(&source, p + 1)) { step(); step(); } }
    unfold(item(&destination, p)); unfold(item(&source, p + 1));
    unfold(slot(&source)); unfold(slot(&destination));
    unfold(authority(slot(&source)));
    unfold(authority(slot(&destination)));
    unfold(authority(item(&source, _)));
    unfold(authority(item(&destination, _)));
    execute(); simp();
}
```

```expect
pass
```
