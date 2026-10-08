# A helper that consumes a member spends it and restores its control

The companion of `authority_helper_consume_without_spend_rejected.md`: the
helper opens the control, spends the consumed member, decrements the C
counter, and restores the control's equation. The caller then observes a
zero count and frees the object.

```c filename=authority_helper_consume_spends_member.c
struct object { int refs; };
void drop(struct object *obj) { obj->refs = obj->refs - 1; }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    drop(obj);
    int left = obj->refs;
    free(obj);
    return left;
}
```

```click
verifying "authority_helper_consume_spends_member.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}
void drop(struct object* obj) {
    owns control(obj);
    consumes reference(obj);
} by {
    unfold(control(obj));
    unfold(reference(obj));
    step();
    fold(control(obj));
    execute();
    simp();
}
int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    fold(control(obj));
    step();
    unfold(control(obj));
    unfold(authority(reference(obj)));
    execute();
    simp();
}
```

```expect
pass
```
