# Field resources view one field and consume another

This checks that a contract can view one struct field and take write
permission for another, and that an explicit range over the whole object
covers every field.

```c filename=field_resources_view_one_field_and_consume_another.c
struct counted {
    int32 ref_count;
    int32 data;
};

int32 copy_count(struct counted* obj) {
    obj->data = obj->ref_count;
    return obj->data;
}

int32 reset(struct counted* obj) {
    obj->ref_count = 0;
    obj->data = 0;
    return 0;
}
```

```click
verifying "field_resources_view_one_field_and_consume_another.c";

int32 copy_count(struct counted* obj) {
    views obj->ref_count;
    consumes obj->data;
    ensures result == obj->ref_count by auto();
}

int32 reset(struct counted* obj) {
    consumes obj[0..1];
    ensures result == 0 by auto();
}
```

```expect
pass
```
