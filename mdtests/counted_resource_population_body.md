# resource bodies describe the whole population

The control resource owns the shared reference-count field and authority for
the population. `count(...)` names the population size, so a function holding
the control and one reference can relate the stored and logical counts.

```c filename=counted_resource_population_body.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj) {
    return obj->refs;
}
```

```click
authorized resource object_ref(obj: struct object*) {}

resource object_control(obj: struct object*) {
    owns obj->refs;
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_population_body.c";

int32 object_refcount(struct object* obj) {
    owns object_control(obj);
    owns object_ref(obj);

    ensures result == count(object_ref(obj));
} by {
    open(object_control(obj)) {
        execute();
    }
    simp();
}
```

```expect
pass
```
