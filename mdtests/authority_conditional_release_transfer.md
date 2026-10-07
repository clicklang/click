# A conditional release returns control only while storage remains live

The unchanged release body handles both final and nonfinal references. Its
contract consumes control and one reference, then returns control only on the
nonfinal branch. The caller preserves payload and observes exactly one fewer
reference through its returned control. No count is observed after retirement.

```c filename=conditional_release.c
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
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}


verifying "conditional_release.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
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
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
} by {
    have obj->refs == count(child_ref(obj)) by { simp(); }
    have 1 < count(child_ref(obj)) by { simp(); }
    step(child_release(obj), {});
    have obj->payload == old(obj->payload) by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
