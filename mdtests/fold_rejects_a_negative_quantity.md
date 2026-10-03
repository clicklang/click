# fold rejects a negative quantity

A resource quantity is a signed `int32`. Authority-mode folding rejects a
negative coefficient before changing either ownership or the population ledger.
Zero remains valid and does not create a member. Counter memory is held
separately from the empty reference family, as in the authority model.

```c filename=fold_rejects_a_negative_quantity.c
struct s { int32 x; };

int32 mint(struct s* o) {
    return 0;
}

int32 mint_zero(struct s* o) {
    return 0;
}
```

```click resource_semantics=authority
resource ref(o: struct s*) {}

verifying "fold_rejects_a_negative_quantity.c";

int32 mint_zero(struct s* o) {
    owns authority(ref(o));
    requires o != 0;
    requires count(ref(o)) == 0;
    owns o->x;
    ensures result == 0;
} by {
    fold(0 of ref(o));
    execute();
    simp();
}

int32 mint(struct s* o) {
    owns authority(ref(o));
    requires o != 0;
    requires count(ref(o)) == 0;
    owns o->x;
    ensures result == 0;
} by {
    fold(-1 of ref(o));
    execute();
    simp();
}
```

```expect
fail: Requires 0 <= -1 (resource quantity)
```
