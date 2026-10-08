# resource population initialization and finalization

The initializer sets the stored count while transferring ordinary memory.
The finalizer consumes the control and last reference, then frees the object.

```c filename=counted_resource_init.c
struct object {
    int32 refs;
};

struct object* object_init(struct object* obj) {
    obj->refs = 1;
    return obj;
}
```

```c filename=counted_resource_finish.c
struct object {
    int32 refs;
};

void object_finish(struct object* obj) {
    obj->refs = 0;
    free(obj);
}
```

```click resource_semantics=authority
authorized resource object_ref(obj: struct object*) {}

resource object_control(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns *obj;
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_init.c";
verifying "counted_resource_finish.c";

struct object* object_init(struct object* obj) {
    consumes allocation(obj, sizeof(struct object));
    consumes *obj;
    produces allocation(obj, sizeof(struct object));
    produces *obj;

    ensures result == obj;
    ensures obj->refs == 1;
} by {
    execute();
    simp();
}

void object_finish(struct object* obj) {
    requires count(object_ref(obj)) == 1;
    consumes object_control(obj);
    consumes object_ref(obj);
} by {
    unfold(object_control(obj));
    unfold(object_ref(obj));
    unfold(authority(object_ref(obj)));
    execute();
    simp();
}
```

```expect
pass
```
