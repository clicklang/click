# Calls preserve framed cells and refresh borrowed counter state

The retaining helper borrows the ordinary counter/authority control, updates
the cell, explicitly creates one member, and returns the restored control.
`count_before_retain` proves the same pre-call value equals the new count minus
one. `restore_around_a_call` temporarily breaks its open control invariant,
calls an unrelated helper, and restores the saved value before closing. The
unrelated call cannot assume the suspended invariant. All C is unchanged.

```c filename=population_call_controls.c
struct object {
    int32 refs;
};

int32 three() {
    return 3;
}

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}

int32 restore_around_a_call(struct object* obj) {
    int32 saved;
    saved = obj->refs;
    obj->refs = 0;
    three();
    obj->refs = saved;
    return saved;
}

int32 count_before_retain(struct object* obj) {
    int32 before;
    before = obj->refs;
    object_retain(obj);
    return before;
}
```

```click
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "population_call_controls.c";

int32 three() {
    ensures result == 3;
} by auto;

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns control(obj);
    produces object_ref(obj);
    ensures result == obj;
} by {
    open(control(obj)) {
        step();
        fold(object_ref(obj));
        execute();
    }
    simp();
}

int32 restore_around_a_call(struct object* obj) {
    owns control(obj);
    ensures result == count(object_ref(obj));
} by {
    open(control(obj)) {
        step();
        step();
        step();
        step();
        step();
    }
    execute();
    simp();
}

int32 count_before_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns control(obj);
    produces object_ref(obj);
    ensures result == count(object_ref(obj)) - 1;
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
pass
```
