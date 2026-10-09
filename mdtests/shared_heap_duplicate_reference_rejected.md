# One increment cannot produce two references

The control ties the C counter to the number of references. A retain that
increments once but claims two new references breaks that tie, so the
control cannot be restored.

```c filename=shared_heap_duplicate_reference_rejected.c
struct child {
    int32 refs;
    int32 payload;
};

void retain_double(struct child* obj) {
    obj->refs = obj->refs + 1;
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

verifying "shared_heap_duplicate_reference_rejected.c";

void retain_double(struct child* obj) {
    requires count(child_ref(obj)) < 2147483646;
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);
    produces child_ref(obj);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_ref(obj));
    fold(child_control(obj));
    execute();
    simp();
}
```

```expect
fail: Requires obj->refs == count(child_ref(obj))
```
