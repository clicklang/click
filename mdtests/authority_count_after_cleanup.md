# An empty population remains observable after free

The exact family whose authority was consumed at zero remains empty. The
proof can use that fact before and after freeing the anchor.

```c filename=spent_count.c
struct object { int32 refs; };
int32 spent_count() {
    struct object* obj = malloc(sizeof(struct object));
    if (obj == 0) { return -1; }
    obj->refs = 0;
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "spent_count.c";

int32 spent_count() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(control(obj));
    unfold(control(obj));
    unfold(authority(reference(obj)));
    have count(reference(obj)) == 0;
    step();
    have count(reference(obj)) == 0;
    execute();
    simp();
}
```

```expect
pass
```
