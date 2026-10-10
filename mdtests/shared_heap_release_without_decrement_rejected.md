# Dropping a reference without decrementing the counter is refused

Consuming a reference changes the population. The C counter must follow, or
the control cannot be restored.

```c filename=shared_heap_release_without_decrement_rejected.c
struct child {
    int32 refs;
    int32 payload;
};

void forget_reference(struct child* obj) {
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

verifying "shared_heap_release_without_decrement_rejected.c";

void forget_reference(struct child* obj) {
    requires 2 <= obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    fold(child_control(obj));
    execute();
    simp();
}
```

```expect
fail: Requires obj->refs == count(child_ref(obj))
```
