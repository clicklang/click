# A nonfinal counted release preserves the underlying allocation

A caller may consume its last owned unit while other counted units remain.
The callee's post-count keeps the population body allocation live, so the
caller's guarded payload guarantee remains readable.

```c filename=counted_release_preserves_nonfinal_allocation.c
struct child { int32 refs; int32 payload; };

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void release_one(struct child* obj) {
    child_release(obj);
}
```

```click resource_semantics=authority
authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}


verifying "counted_release_preserves_nonfinal_allocation.c";

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


void release_one(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    have obj->refs == count(child_ref(obj));
    have 1 < count(child_ref(obj));
    step(child_release(obj), {});
    have obj->payload == old(obj->payload);
    step();
    simp();
}
```

```expect
pass
```
