# A static struct's fields by declaration reference

A static object's declaration reference names the object, so its fields are
read with `.`: `"file.c"::static(0).field` for a file static and
`f.static(0).field` for a function static. The read is a load from the
static's storage at the selected state, as `(&"file.c"::static(0))->field`
is. It is not the entry value of a by-value aggregate parameter, though the
entry state binds a static struct as an aggregate object. A function static
written by the call reads its new value, and the last function's claim, that
the call leaves the old value, is refused.

```c filename=static_fields.c
struct pair { int32 a; int32 b; };

static const struct pair limits = { .a = 3, .b = 5 };

int32 upper() {
    return limits.b;
}

void remember(int32 v) {
    static struct pair last;
    last.b = v;
}

void remember_wrong(int32 v) {
    static struct pair last;
    last.b = v;
}
```

```click
verifying "static_fields.c";

int32 upper() {
    views limits.b;
    ensures result == "static_fields.c"::static(0).b;
    ensures result == 5;
}

void remember(int32 v) {
    owns remember.static(0);
    ensures remember.static(0).b == v;
}

void remember_wrong(int32 v) {
    owns remember_wrong.static(0);
    ensures remember_wrong.static(0).b == old(remember_wrong.static(0).b);
}
```

```expect
fail: remember_wrong
```
