# A linked pointer cannot recreate a released child reference

The caller releases both counted units before detach. The parent still
points at `kid`, but its pointer value cannot create a missing `child_ref(kid)`
unit for the detach contract.

The extra release spends the last member and retires control. Detach must
therefore refuse the already retired child's control at its original call site.

```c filename=shared_heap_missing_child_ref.c
struct child { int32 refs; int32 payload; };
struct parent { struct child* kid; };
void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void child_release(struct child* obj) {
    if (obj->refs == 1) { free(obj); }
    else { obj->refs = obj->refs - 1; }
}
void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}
void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    free(p);
}
int32 caller(struct child* kid) {
    struct parent* p = malloc(sizeof(struct parent));
    if (p == 0) {
        child_release(kid);
        return -1;
    }
    parent_attach(p, kid);
    child_release(kid);
    child_release(kid);
    parent_detach(p);
    return 0;
}
```

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {
            owns p->kid;
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_missing_child_ref.c";

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_control(obj);
    produces child_ref(obj);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
    execute();
    simp();
}

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

void parent_attach(struct parent* p, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    requires kid != 0;
    consumes p->kid;
    owns child_control(kid);
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
} by {
    step();
    step();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    execute();
    simp();
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_control(p->kid);
    if old(count(child_ref(p->kid))) > 1 { produces child_control(old(p->kid)); }
    consumes child_ref(p->kid);
    consumes allocation(p, sizeof(struct parent));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by simp;
            if p->kid->refs > 1 {
                execute();
                simp();
            } else {
                execute();
                simp();
            }
        },
    }
}

int32 caller(struct child* kid) {
    requires kid != 0;
    requires count(child_ref(kid)) == 1;
    consumes child_control(kid);
    consumes child_ref(kid);
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then {
        step(child_release(kid), {});
        step();
        simp();
    } else {}
    let { link: link } = step(parent_attach(p, kid), {});
    have count(child_ref(kid)) == 2 by { simp(); }
    have kid->refs == count(child_ref(kid)) by { simp(); }
    step(child_release(kid), {});
    have count(child_ref(kid)) == 1 by { simp(); }
    have kid->refs == count(child_ref(kid)) by { simp(); }
    step(child_release(kid), {});
    step(parent_detach(p), { link: link });
    step();
    simp();
}

```

```expect
fail: missing resource fact `owns child_control(kid)`
```
