# Control bodies open without changing their population count

An ordinary control owns the counter cell and population authority. Scoped
opening exposes that body without creating or consuming a reference member,
and closing restores its exact counter/count relation. The C is unchanged.

```c filename=resource_population_open.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj) {
    return obj->refs;
}
```

```click resource_semantics=authority
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "resource_population_open.c";

int32 object_refcount(struct object* obj) {
    owns control(obj);

    ensures result == count(object_ref(obj));
} by {
    open(control(obj)) {
        execute();
    }
    simp();
}
```

```expect
pass
```
