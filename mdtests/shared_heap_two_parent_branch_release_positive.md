# Two parents compose through one branch-on-count child release

The creator starts with one reference, each attach retains one, and each
subsequent release consumes exactly one. The first parent detaches, the second
still reads the payload, and the final detach frees the child. The detach
contract returns the parent link and relies on the checked counted-resource
transition; it does not need a redundant pure count postcondition through the
field after that field is cleared.

```c filename=shared_heap_two_parent_branch_release.c
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

void caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 observed = parent_read_payload(second);
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
            owns &p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_two_parent_branch_release.c";

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
    consumes &p->kid;
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
    ensures result == old(p->kid->payload);
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
    if old(count(child_ref(p->kid))) > 1 { produces child_control(old(p->kid)); }
    consumes child_ref(p->kid);
    produces out: parent(old(p));
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

void caller(struct parent* first, struct parent* second, struct child* kid) {
    consumes &first->kid;
    consumes &second->kid;
    requires kid != 0;
    requires count(child_ref(kid)) == 1;
    requires kid->refs == 1;
    consumes child_control(kid);
    consumes child_ref(kid);
} by {
    let { link: first_link } = step(parent_attach(first, kid), {});
    have count(child_ref(kid)) == 2 by simp;
    let { link: second_link } = step(parent_attach(second, kid), {});
    have count(child_ref(kid)) == 3 by simp;
    step(child_release(kid), {});
    have count(child_ref(kid)) == 2 by simp;
    let first_out = step(parent_detach(first), { link: first_link });
    step();
    have count(child_ref(kid)) == 1 by simp;
    step(parent_read_payload(second), { link: second_link });
    have second->kid == kid by simp;
    let second_out = step(parent_detach(second), { link: second_link });
    step();
    simp();
}
```

```expect
pass
```
