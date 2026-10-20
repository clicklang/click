# a contract produces a resource over a field of a struct it returns

A struct returned by value is a fresh object the abstract machine creates for
the caller, which no resource names. A contract may still produce a resource
over one of its fields, `produces cell(result.p)`: the caller reads the field
to evaluate the clause, then copies the struct out, and holds the resource at
the copied pointer. This is how a Rust `Stack::new()` hands its caller the
list its returned stack owns.

```c filename=c_produced_resource_over_returned_struct_field.c
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

verifying "c_produced_resource_over_returned_struct_field.c";

struct holder wrap(int32* p) {
    consumes cell(p);
    produces cell(result.p);
    ensures result.p == p;
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
pass
```
