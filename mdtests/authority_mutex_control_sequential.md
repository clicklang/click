# A mutex-ready control is also an ordinary sequential resource

The same field-bearing control used with a mutex needs no mutex. Its
creator folds it, opens it to create and later spend a member, and checks
its counter equation at each fold.

```c filename=authority_mutex_control_sequential.c
struct object { int refs; };
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    obj->refs = obj->refs + 1;
    obj->refs = obj->refs - 1;
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
verifying "authority_mutex_control_sequential.c";
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}

int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    let control = fold(control(obj), { refs: 0 });
    unfold(control);
    step();
    fold(reference(obj));
    have count(reference(obj)) == 1;
    let control = fold(control(obj), { refs: 1 });
    unfold(control);
    unfold(reference(obj));
    step();
    let control = fold(control(obj), { refs: 0 });
    unfold(control);
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
pass
```
