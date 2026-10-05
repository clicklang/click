# An unrelated call cannot assume an open control invariant

The caller holds one reference member and opens its separate counter/authority
control. It writes zero while the population remains positive, then calls an
unrelated helper. That call cannot certify the suspended control invariant or
use its contradiction to prove the false result claim. Closing requires the
actual counter/count relation, which is not restored. The C is unchanged.

```c filename=call_inside_open_population.c
struct object {
    int32 refs;
};

int32 three() {
    return 3;
}

int32 broken(struct object* obj) {
    obj->refs = 0;
    three();
    return 0;
}
```

```click resource_semantics=authority
resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "call_inside_open_population.c";

int32 three() {
    ensures result == 3;
} by auto;

int32 broken(struct object* obj) {
    owns control(obj);
    owns object_ref(obj);
    ensures result == 1;
} by {
    open(control(obj)) {
        step();
        step();
    }
    execute();
    simp();
}
```

```expect
fail: Requires obj->refs == count(object_ref(obj))
```
