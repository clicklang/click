# Shared-parent lifecycles preserve the payload and reclaim the final child

The unchanged C exercises both destruction orders, all allocation failures,
the surviving parent's payload read, and final reclamation. Count observations
and transitions resolve proved aliases to the same population ledger entry.
The final detach removes that entry rather than leaving a stale body invariant
for certification to demand after free.

```c filename=shared_parent.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_init(struct child* obj, int32 payload) {
    obj->refs = 1;
    obj->payload = payload;
}

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

int32 run_first_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 out = parent_read_payload(second);
    parent_detach(second);
    free(first);
    free(second);
    return out;
}

int32 run_second_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(second);
    int32 out = parent_read_payload(first);
    parent_detach(first);
    free(first);
    free(second);
    return out;
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

authorized resource child_ref(obj: struct child*) {}

resource child_storage(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_parent.c";

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

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);
    ensures obj->payload == old(obj->payload);
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

void parent_attach(struct parent* p, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    requires kid != 0;
    requires separate(memory(p->kid), memory(kid->payload));
    consumes p->kid;
    owns child_control(kid);
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures p->kid == kid;
    ensures kid->payload == old(kid->payload);
} by {
    execute();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    simp();
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
    ensures result == old(p->kid->payload);
    ensures p->kid == old(p->kid);
    ensures link.link == old(link.link);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by { simp(); }
            open(child_control(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(kid) });
            simp();
        },
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
    produces p->kid;
    ensures old(count(child_ref(p->kid))) > 1 implies old(p->kid)->payload == old(p->kid->payload);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by simp;
            have old(p->kid->refs) == old(count(child_ref(p->kid))) by { simp(); }
            step();
            have kid->refs == old(p->kid->refs) by { simp(); }
            if kid->refs > 1 {
                have old(count(child_ref(p->kid))) > 1 by { simp(); }
                execute();
                simp();
            } else {
                have old(count(child_ref(p->kid))) == kid->refs by { simp(); }
                have old(count(child_ref(p->kid))) <= 1 by {
                    rewrite(old(count(child_ref(p->kid))) == kid->refs);
                    simp();
                }
                execute();
                have old(count(child_ref(p->kid))) > 1 implies old(p->kid)->payload == old(p->kid->payload) by {
                    intro();
                    contradiction(old(count(child_ref(p->kid))) <= 1);
                }
                simp();
            }
        },
    }
}

int32 run_first_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
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
    branch then { step(); step(); step(); simp(); } else {}
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    step(child_release(kid), {});
    have first->kid == kid by { simp(); }
    have kid->payload == payload by { simp(); }
    open(child_control(kid)) {
        have count(child_ref(first->kid)) > 1 by { simp(); }
        have 1 <= first->kid->refs by { rewrite(first->kid == kid); simp(); }
    }
    have first->kid->payload == payload by { rewrite(first->kid == kid); simp(); }
    mark detaching;
    step(parent_detach(first), { link: first_link });
    have at(detaching, first->kid) == kid by { assumption(); }
    have at(detaching, first->kid)->payload == at(detaching, first->kid->payload) by { simp(); }
    have at(detaching, first->kid->payload) == payload by { assumption(); }
    have at(detaching, first->kid)->payload == payload by {
        simp() using {
            at(detaching, first->kid)->payload == at(detaching, first->kid->payload);
            at(detaching, first->kid->payload) == payload;
        }
    }
    have kid->payload == payload by {
        have kid == at(detaching, first->kid) by { simp() using { at(detaching, first->kid) == kid; } }
        rewrite(kid == at(detaching, first->kid));
        assumption();
    }
    step();
    have second->kid == kid by { simp(); }
    have second->kid->payload == payload by { rewrite(second->kid == kid); simp(); }
    mark reading;
    step(parent_read_payload(second), { link: second_link });
    have at(reading, second->kid->payload) == payload by { assumption(); }
    have out == at(reading, second->kid->payload) by { simp(); }
    have out == payload by { simp(); }
    have second->kid == kid by { simp(); }
    open(child_control(kid)) {
        have 1 <= second->kid->refs by { rewrite(second->kid == kid); simp(); }
    }
    step(parent_detach(second), { link: second_link });
    step();
    step();
    step();
    simp();
}

int32 run_second_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
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
    branch then { step(); step(); step(); simp(); } else {}
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    step(child_release(kid), {});
    have second->kid == kid by { simp(); }
    have kid->payload == payload by { simp(); }
    open(child_control(kid)) {
        have count(child_ref(second->kid)) > 1 by { simp(); }
        have 1 <= second->kid->refs by { rewrite(second->kid == kid); simp(); }
    }
    have second->kid->payload == payload by { rewrite(second->kid == kid); simp(); }
    mark detaching;
    step(parent_detach(second), { link: second_link });
    have at(detaching, second->kid) == kid by { assumption(); }
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload) by { simp(); }
    have at(detaching, second->kid->payload) == payload by { assumption(); }
    have at(detaching, second->kid)->payload == payload by {
        simp() using {
            at(detaching, second->kid)->payload == at(detaching, second->kid->payload);
            at(detaching, second->kid->payload) == payload;
        }
    }
    have kid->payload == payload by {
        have kid == at(detaching, second->kid) by { simp() using { at(detaching, second->kid) == kid; } }
        rewrite(kid == at(detaching, second->kid));
        assumption();
    }
    step();
    have first->kid == kid by { simp(); }
    have first->kid->payload == payload by { rewrite(first->kid == kid); simp(); }
    mark reading;
    step(parent_read_payload(first), { link: first_link });
    have at(reading, first->kid->payload) == payload by { assumption(); }
    have out == at(reading, first->kid->payload) by { simp(); }
    have out == payload by { simp(); }
    have first->kid == kid by { simp(); }
    open(child_control(kid)) {
        have 1 <= first->kid->refs by { rewrite(first->kid == kid); simp(); }
    }
    step(parent_detach(first), { link: first_link });
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
