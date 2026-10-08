# Two parent links share one child resource

The caller starts with the creator's one reference. Its explicit population
precondition records that total; borrowing control alone permits an arbitrary
entry population.

Here `child_release` only decrements and requires a total above one, so it
borrows and preserves control. `parent_detach` borrows one surviving reference and consumes one other
reference; the total therefore remains positive, and it returns control
unconditionally through the original child pointer after clearing the parent
field. These contracts preserve the original inputs and strengthen the
resource return guarantee without changing C or the payload claim.

```c filename=shared_heap_two_parent_caller.c
struct child { int32 refs; int32 payload; };
struct parent { struct child* kid; };

void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void child_release(struct child* obj) { obj->refs = obj->refs - 1; }
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
int32 caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    parent_detach(first);
    int32 observed = parent_read_payload(second);
    parent_detach(second);
    return observed;
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

verifying "shared_heap_two_parent_caller.c";

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
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs by simp;
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
    ensures result == p->kid->payload;
    ensures p->kid == old(p->kid);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            open(child_control(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(p->kid) });
            simp();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_control(p->kid);
    produces child_control(old(p->kid));
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(old(p));
    ensures old(p->kid)->payload == old(p->kid->payload);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have 2 <= old(count(child_ref(p->kid))) by simp;
            have old(count(child_ref(p->kid))) > 1 by {
                simp() using { 2 <= old(count(child_ref(p->kid))); }
            }
            step();
            step();
            step();
            let out = fold(parent(p), { link: ParentLink::Empty });
            execute();
            simp();
        },
    }
}

int32 caller(struct parent* first, struct parent* second, struct child* kid) {
    consumes first->kid;
    consumes second->kid;
    requires kid != 0;
    requires count(child_ref(kid)) == 1;
    owns child_control(kid);
    owns child_ref(kid);
    ensures result == kid->payload;
} by {
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    let first_out = step(parent_detach(first), { link: first_link });
    step();
    step(parent_read_payload(second), { link: second_link });
    have second->kid == kid by simp;
    have observed == kid->payload by simp;
    have observed == second->kid->payload by { rewrite(second->kid == kid); simp(); }
    mark detaching;
    let second_out = step(parent_detach(second), { link: second_link });
    have at(detaching, second->kid) == kid by { assumption(); }
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload) by { simp(); }
    have observed == at(detaching, second->kid->payload) by { assumption(); }
    have kid == at(detaching, second->kid) by { simp() using { at(detaching, second->kid) == kid; } }
    have kid->payload == at(detaching, second->kid->payload) by {
        rewrite(kid == at(detaching, second->kid));
        assumption();
    }
    step();
    simp();
}
```

```expect
pass
```
