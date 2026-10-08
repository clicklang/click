# resource populations finalize independently

Ending one resource population must not consume the control or reference
belonging to another population mentioned by the same function.

```c filename=counted_resource_finish_one.c
struct object {
    int32 refs;
};

void object_finish_one(struct object* finished, struct object* kept) {
    finished->refs = 0;
    free(finished);
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

verifying "counted_resource_finish_one.c";

void object_finish_one(struct object* finished, struct object* kept) {
    requires finished != kept;
    requires count(object_ref(finished)) == 1;
    consumes object_control(finished);
    consumes object_ref(finished);
    owns object_control(kept);
    owns object_ref(kept);
} by {
    unfold(object_control(finished));
    unfold(object_ref(finished));
    unfold(authority(object_ref(finished)));
    execute();
    simp();
}
```

```expect
pass
```
