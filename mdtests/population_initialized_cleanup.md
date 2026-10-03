# Initialized population observations survive allocation and cleanup

Explicit initialization is a body fact, separate from membership and value
equality. Both results of an unrelated allocation preserve the child's
initialized reads. The final release still discharges the allocation.

```c filename=cleanup.c
struct child { int32 refs; int32 payload; };
void child_init(struct child* obj, int32 payload) {
    obj->refs = 1;
    obj->payload = payload;
}
void child_release(struct child* obj) {
    if (obj->refs == 1) { free(obj); }
    else { obj->refs = obj->refs - 1; }
}
int32 cleanup(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) { return -1; }
    child_init(kid, payload);
    int32* other = malloc(sizeof(int32));
    if (other == 0) { child_release(kid); return -1; }
    child_release(kid);
    free(other);
    return 0;
}
```

```click resource_semantics=authority
resource child_ref(obj: struct child*) {}

resource child_storage(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
}

resource child_control(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "cleanup.c";

void child_init(struct child* obj, int32 payload) {
    requires count(child_ref(obj)) == 0;
    owns child_storage(obj);
    produces child_ref(obj);
    ensures obj->refs == 1;
    ensures defined(obj->refs);
    ensures defined(obj->payload);
    ensures obj->payload == payload;
} by {
    unfold(child_storage(obj));
    step();
    step();
    fold(child_ref(obj));
    fold(child_storage(obj));
    execute();
    simp();
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
    ensures old(count(child_ref(obj))) > 1 implies obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        execute();
        simp();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            arithmetic() using { 1 <= obj->refs; obj->refs != 1; }
        }
        have obj->refs - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
                1 < obj->refs;
            }
        }
        step();
        step();
        fold(child_control(obj));
        execute();
        simp();
    }
}

int32 cleanup(int32 payload) {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    fold(authority(child_ref(kid)));
    fold(child_storage(kid));
    step();
    unfold(child_storage(kid));
    fold(child_control(kid));
    step();
    step();
    branch then { step(); step(); simp(); } else {}
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
