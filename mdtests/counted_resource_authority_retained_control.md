# Retained authority control passes certification

A proof that retains a folded control must certify its return without asking
the legacy population body transition to unfold its contained authority.

```c filename=counted_resource_retained_control.c
struct object { int32 refs; };
void keep_control(struct object* first) {}
```

```click resource_semantics=authority
authorized resource object_ref(obj: struct object*) {}
resource object_control(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}
verifying "counted_resource_retained_control.c";
void keep_control(struct object* first) {
    owns object_control(first);
    owns object_ref(first);
} by {
    execute();
    simp();
}
```

```expect
pass
```
