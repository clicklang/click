# a resource over a returned struct's field is held at that field's value

The resource a contract produces over `result.p` is held at the value the
returned field has, and nothing else. Without `ensures result.p == p` the
caller cannot tell that value is `p`, so it cannot give back `cell(p)`.


```c filename=c_produced_resource_over_returned_struct_field_is_only_that_field.c
struct holder {
    int32 *p;
};

struct holder wrap(int32 *p) {
    struct holder h;
    h.p = p;
    return h;
}

int32 rewrap(int32 *p) {
    struct holder h = wrap(p);
    return 0;
}
```

```click
resource cell(q: int32*) {
    owns *q;
}

verifying "c_produced_resource_over_returned_struct_field_is_only_that_field.c";

struct holder wrap(int32* p) {
    consumes cell(p);
    produces cell(result.p);
} by {
    execute();
}

int32 rewrap(int32* p) {
    owns cell(p);
    ensures result == 0;
} by {
    execute();
}
```

```expect
fail: missing resource fact
```
