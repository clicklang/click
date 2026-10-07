# A branch-on-count release consumes one of an unknown population

The release consumes one reference from an arbitrary population. Its control
resource supplies the allocation and count invariant, returns on the non-final
branch, and retires with the allocation on the final branch. Both paths preserve
the exact count decrement guarantee.

```c filename=child_release_branch_on_count.c
struct child {
    int32 refs;
};

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
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

verifying "child_release_branch_on_count.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 { produces child_control(obj); }
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
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
            apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using { 1 < obj->refs; }
        }
        step();
        step();
        fold(child_control(obj));
        execute();
        simp();
    }
}
```

```expect
pass
```
