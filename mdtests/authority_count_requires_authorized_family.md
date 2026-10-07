# Counting an unauthorized family is refused

Only an `authorized resource` family has a population count. `reference`
is an ordinary resource here, so `count(reference(obj))` is refused.

```c filename=spent_count.c
struct object { int32 refs; };
int32 spent_count() {
    struct object* obj = malloc(sizeof(struct object));
    if (obj == 0) { return -1; }
    obj->refs = 0;
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}

verifying "spent_count.c";

int32 spent_count() {
    ensures result == -1 or result == 0;
}
```

```expect
fail: `count` names `reference`, which is not an authorized family
```
