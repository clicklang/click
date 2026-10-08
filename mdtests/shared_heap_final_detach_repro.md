# Final parent detach must account for the conditional child release

```c filename=shared_heap_final_detach.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

void caller(struct parent* p, struct child* kid) {
    parent_detach(p);
}
```

```click resource_semantics=authority
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_final_detach.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
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

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires 1 <= p->kid->refs;
    consumes child_control(p->kid);
    consumes child_ref(p->kid);
    if old(count(child_ref(p->kid))) > 1 {
        produces child_control(old(p->kid));
    }
    produces out: parent(old(p));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            step();
            if kid->refs > 1 {
                execute();
                let out = fold(parent(p), { link: ParentLink::Empty });
                simp();
            } else {
                execute();
                let out = fold(parent(p), { link: ParentLink::Empty });
                simp();
            }
        },
    }
}

void caller(struct parent* p, struct child* kid) {
    consumes p->kid;
    requires kid != 0;
    requires p->kid == kid;
    requires kid->refs == 1;
    consumes child_control(kid);
    consumes child_ref(kid);
} by {
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    let out = step(parent_detach(p), { link: link });
    step();
    simp();
}
```

```expect
pass
```
