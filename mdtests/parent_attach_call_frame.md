# A parent link survives a disjoint retain call before folding

The attach helper writes the parent link, calls a helper that mutates only the
child's reference count, and then folds the parent resource. The fold needs the
pointer-valued field fact established before the call.

The caller starts with the creator's one reference. Its explicit population
precondition records that total; borrowing control alone permits an arbitrary
entry population.

```c filename=parent_attach_call_frame.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

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

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

void caller(struct parent* p, struct child* kid) {
    parent_attach(p, kid);
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

verifying "parent_attach_call_frame.c";

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
    requires 1 < count(child_ref(obj));
    consumes child_control(obj);
    if old(count(child_ref(obj))) > 1 { produces child_control(obj); }
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs;
    have obj->refs - 1 >= 1 by {
        apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using { 1 < obj->refs; }
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
    ensures p->kid == kid;
} by {
    step();
    step();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    execute();
    simp();
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(attached) => {
            unfold(link);
            open(child_control(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(p->kid) });
            simp();
        },
    }
}

void caller(struct parent* p, struct child* kid) {
    consumes p->kid;
    requires kid != 0;
    requires count(child_ref(kid)) == 1;
    owns child_control(kid);
    owns child_ref(kid);
} by {
    let { link: link } = step(parent_attach(p, kid), {});
    unfold(link);
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    step();
    simp();
}
```

```expect
pass
```
