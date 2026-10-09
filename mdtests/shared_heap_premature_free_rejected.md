# Freeing a shared child before its last reference is refused

While another reference is outstanding the child must stay allocated. Freeing
it directly would leave that reference dangling, so the authority over the
references cannot be discarded.

```c filename=shared_heap_premature_free_rejected.c
struct child {
    int32 refs;
    int32 payload;
};

void free_early(struct child* obj) {
    free(obj);
}
```

```click
authorized resource child_ref(obj: struct child*) {}

resource child_storage(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_premature_free_rejected.c";

void free_early(struct child* obj) {
    requires obj->refs == 2;
    consumes child_control(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    execute();
    simp();
}
```

```expect
fail: Requires consumes authority(child_ref(...))
```
