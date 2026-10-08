# Creator reference release after two produced parent links

This is the smallest composition shape from the frozen shared-heap graph:
two attaches produce parent resources that both point at `kid`, then the
caller releases its original creator reference.

The `owns child_ref(p->kid)` clause already returns the borrowed survivor.
The detach contract consumes its additional member and does not also promise
a duplicate produced member after clearing the field.

The caller requires room for both attaches' signed counter increments.
Its two local members do not bound the total held by other callers.

```c filename=shared_heap_creator_release_repro.c
struct child { int32 refs; };
struct parent { struct child* kid; };

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    obj->refs = obj->refs - 1;
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    parent_detach(second);
}
```

```click resource_semantics=authority
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
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
    fact defined(obj->refs);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_creator_release_repro.c";

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_control(obj);
    owns child_ref(obj);
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
    requires 1 < count(child_ref(obj));
    owns child_control(obj);
    owns child_ref(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs;
    have obj->refs - 1 >= 1 by {
        apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
            1 < obj->refs;
        }
    }
    step();
    fold(child_control(obj));
    execute();
    simp();
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
    execute();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    simp();
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(old(p));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            execute();
            let out = fold(parent(p), { link: ParentLink::Empty });
            simp();
        },
    }
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    consumes first->kid;
    consumes second->kid;
    requires kid != 0;
    requires count(child_ref(kid)) < 2147483646;
    owns child_control(kid);
    owns child_ref(kid);
    consumes child_ref(kid);
} by {
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    step(child_release(kid), {});
    let first_out = step(parent_detach(first), { link: first_link });
    let second_out = step(parent_detach(second), { link: second_link });
    step();
    simp();
}
```

```expect
pass
```
