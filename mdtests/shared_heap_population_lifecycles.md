# Shared-parent lifecycles preserve the payload and reclaim the final child

The unchanged C exercises both destruction orders, all allocation failures,
the surviving parent's payload read, and final reclamation. The control resource
equates the child's reference field with its population count. Detach uses
an exact entry read for its ownership guard and payload guarantee. The callers
use the same read through either parent link and preserve it across the
assignment of the payload reader's result. The final detach removes the
population entry when it frees the child.

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

```click
import click::integer;

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
    fact to_integer(obj->refs) == to_integer(count(child_ref(obj)));
}

verifying "shared_parent.c";

void child_init(struct child* obj, int32 payload) {
    requires to_integer(count(child_ref(obj))) == 0;
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
}

void child_retain(struct child* obj) {
    requires to_integer(count(child_ref(obj))) < 2147483647;
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures to_integer(count(child_ref(obj))) == to_integer(old(count(child_ref(obj))) - 1);
    ensures to_integer(old(count(child_ref(obj)))) > 1 implies obj->payload == old(obj->payload);
    ensures to_integer(old(count(child_ref(obj)))) > 1 implies
        to_integer(exact(obj->refs)) == to_integer(count(child_ref(obj)));
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        close();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            apply(click::integer::int32_less_equal_and_not_equal_implies_less_than(1, obj->refs));
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        close();
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    requires to_integer(count(child_ref(kid))) < 2147483647;
    requires kid != 0;
    requires separate(memory(p->kid), memory(kid->payload));
    consumes uninitialized(p->kid);
    owns child_control(kid);
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures p->kid == kid;
    ensures kid->payload == old(kid->payload);
} by {
    step_until(function.exit);
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    close();
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
    ensures exact(p->kid->refs) == p->kid->refs;
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have old(p->kid) == entry_child;
            with(child_control(p->kid)) {
                step_until(function.exit);
                have exact(p->kid->refs) == p->kid->refs by { close(); }
            }
            let link = fold(parent(p), { link: ParentLink::Linked(entry_child) });
            close();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires 1 <= p->kid->refs;
    consumes child_control(p->kid);
    consumes child_ref(p->kid);
    if old(exact(p->kid->refs)) > 1 {
        produces child_control(old(p->kid));
    }
    produces p->kid;
    ensures old(exact(p->kid->refs)) > 1 implies old(p->kid)->payload == old(p->kid->payload);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have old(p->kid) == entry_child;
            have to_integer(old(p->kid->refs)) == to_integer(old(count(child_ref(p->kid))));
            have old(exact(p->kid->refs)) == old(p->kid->refs) by { close(); }
            step();
            have entry_child->refs == old(p->kid->refs);
            if entry_child->refs > 1 {
                have to_integer(old(count(child_ref(p->kid)))) > 1;
                step_until(statement(2).entry);
                have kid == old(p->kid) by { close(); }
                with(child_control(kid)) {
                    have kid->payload == old(p->kid->payload) by { close(); }
                    have separate(memory(p->kid), memory(*kid)) by { close(); }
                    have contains(memory(*kid), memory(kid->payload)) by { normalize(); }
                    apply(click::separation::contains_refl(memory(p->kid)));
                    apply(click::separation::separate_restrict(memory(p->kid), memory(*kid),
                        memory(p->kid), memory(kid->payload)));
                    mark before_clear;
                    step();
                    have separate(statement(2).footprint, memory(kid->payload)) by {
                        normalize() using { at(before_clear, separate(memory(p->kid), memory(kid->payload))); };
                    }
                    have kid->payload == at(before_clear, kid->payload) by {
                        preserve(memory(kid->payload), statement(2));
                    }
                    have kid->payload == old(p->kid->payload) by {
                        rewrite(kid->payload, at(before_clear, kid->payload));
                        close();
                    }
                }
                have old(p->kid)->payload == old(p->kid->payload) by { rewrite(old(p->kid), kid); close(); }
                step_until(function.exit);
                close();
            } else {
                have to_integer(old(count(child_ref(p->kid)))) == to_integer(entry_child->refs);
                have to_integer(old(count(child_ref(p->kid)))) <= 1 by {
                    rewrite(to_integer(old(count(child_ref(p->kid)))), to_integer(entry_child->refs));
                    close();
                }
                step_until(function.exit);
                have to_integer(old(count(child_ref(p->kid)))) > 1 implies old(p->kid)->payload == old(p->kid->payload) by {
                    intro() {
                        contradiction(to_integer(old(count(child_ref(p->kid)))) <= 1);
                    }
                }
                close();
            }
        },
    }
}

int32 run_first_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    fold(authority(child_ref(kid)));
    fold(child_storage(kid));
    step();
    unfold(child_storage(kid));
    fold(child_control(kid));
    step();
    step();
    branch { true => { step(); step(); close(); } false => {} }
    step();
    step();
    branch { true => { step(); step(); step(); close(); } false => {} }
    let { link: first_link } = step(parent_attach);
    let { link: second_link } = step(parent_attach);
    step(child_release);
    have first->kid == kid by { close(); }
    have exact(first->kid->refs) == exact(kid->refs) by { rewrite(first->kid, kid); close(); }
    have exact(kid->refs) == 2 by { close(); }
    have exact(first->kid->refs) == 2 by { close(); }
    have exact(first->kid->refs) > 1 by { rewrite(exact(first->kid->refs), 2); close(); }
    have kid->payload == payload;
    have first->kid->payload == payload by { rewrite(first->kid, kid); close(); }
    mark detaching;
    step(parent_detach, { link: first_link });
    have at(detaching, first->kid) == kid by close();
    have at(detaching, exact(first->kid->refs)) > 1 by { close(); }
    have at(detaching, first->kid)->payload == at(detaching, first->kid->payload) by {
        apply(at(detaching, exact(first->kid->refs)) > 1 implies
            at(detaching, first->kid)->payload == at(detaching, first->kid->payload));
    }
    have at(detaching, first->kid->payload) == payload by close();
    have at(detaching, first->kid)->payload == payload by {
        close() using {
            at(detaching, first->kid)->payload == at(detaching, first->kid->payload);
            at(detaching, first->kid->payload) == payload;
        };
    }
    have kid->payload == payload by {
        have kid == at(detaching, first->kid) by { close() using { at(detaching, first->kid) == kid; }; }
        rewrite(kid, at(detaching, first->kid));
        close();
    }
    step();
    have second->kid == kid;
    have second->kid->payload == payload by { rewrite(second->kid, kid); close(); }
    mark reading;
    let { result: observed } = step(parent_read_payload, { link: second_link });
    have observed == at(reading, second->kid->payload) by { close(); }
    have at(reading, second->kid->payload) == payload by { close(); }
    have observed == payload by { close(); }
    mark after_read;
    step();
    have second->kid == kid by { close(); }
    have at(after_read, separate(memory(out), memory(kid->refs))) by { normalize(); }
    have separate(statement(11).assignment(out, 0).footprint, memory(kid->refs)) by {
        normalize() using { at(after_read, separate(memory(out), memory(kid->refs))); };
    }
    have separate(statement(11).assignment(out, 0).footprint, memory(second->kid->refs)) by {
        rewrite(second->kid, kid);
        close();
    }
    have exact(second->kid->refs) == at(after_read, exact(second->kid->refs)) by {
        preserve(memory(second->kid->refs), statement(11).assignment(out, 0));
    }
    have out == observed by { close(); }
    have out == payload by { close(); }
    with(child_control(kid)) {
        have to_integer(count(child_ref(kid))) == 1 by { normalize(); }
        have to_integer(kid->refs) == 1 by {
            rewrite(to_integer(kid->refs), to_integer(count(child_ref(kid))));
            close();
        }
        have second->kid->refs == 1 by { rewrite(second->kid, kid); close(); }
        have exact(second->kid->refs) <= 1 by {
            have at(after_read, exact(second->kid->refs)) == second->kid->refs by { close(); }
            rewrite(exact(second->kid->refs), at(after_read, exact(second->kid->refs)));
            rewrite(at(after_read, exact(second->kid->refs)), second->kid->refs);
            rewrite(second->kid->refs, 1);
            close();
        }
    }
    step(parent_detach, { link: second_link });
    step();
    step();
    step();
    close();
}

int32 run_second_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    fold(authority(child_ref(kid)));
    fold(child_storage(kid));
    step();
    unfold(child_storage(kid));
    fold(child_control(kid));
    step();
    step();
    branch { true => { step(); step(); close(); } false => {} }
    step();
    step();
    branch { true => { step(); step(); step(); close(); } false => {} }
    let { link: first_link } = step(parent_attach);
    let { link: second_link } = step(parent_attach);
    step(child_release);
    have second->kid == kid by { close(); }
    have exact(second->kid->refs) == exact(kid->refs) by { rewrite(second->kid, kid); close(); }
    have exact(kid->refs) == 2 by { close(); }
    have exact(second->kid->refs) == 2 by { close(); }
    have exact(second->kid->refs) > 1 by { rewrite(exact(second->kid->refs), 2); close(); }
    have kid->payload == payload;
    have second->kid->payload == payload by { rewrite(second->kid, kid); close(); }
    mark detaching;
    step(parent_detach, { link: second_link });
    have at(detaching, second->kid) == kid by close();
    have at(detaching, exact(second->kid->refs)) > 1 by { close(); }
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload) by {
        apply(at(detaching, exact(second->kid->refs)) > 1 implies
            at(detaching, second->kid)->payload == at(detaching, second->kid->payload));
    }
    have at(detaching, second->kid->payload) == payload by close();
    have at(detaching, second->kid)->payload == payload by {
        close() using {
            at(detaching, second->kid)->payload == at(detaching, second->kid->payload);
            at(detaching, second->kid->payload) == payload;
        };
    }
    have kid->payload == payload by {
        have kid == at(detaching, second->kid) by { close() using { at(detaching, second->kid) == kid; }; }
        rewrite(kid, at(detaching, second->kid));
        close();
    }
    step();
    have first->kid == kid;
    have first->kid->payload == payload by { rewrite(first->kid, kid); close(); }
    mark reading;
    let { result: observed } = step(parent_read_payload, { link: first_link });
    have observed == at(reading, first->kid->payload) by { close(); }
    have at(reading, first->kid->payload) == payload by { close(); }
    have observed == payload by { close(); }
    mark after_read;
    step();
    have first->kid == kid by { close(); }
    have at(after_read, separate(memory(out), memory(kid->refs))) by { normalize(); }
    have separate(statement(11).assignment(out, 0).footprint, memory(kid->refs)) by {
        normalize() using { at(after_read, separate(memory(out), memory(kid->refs))); };
    }
    have separate(statement(11).assignment(out, 0).footprint, memory(first->kid->refs)) by {
        rewrite(first->kid, kid);
        close();
    }
    have exact(first->kid->refs) == at(after_read, exact(first->kid->refs)) by {
        preserve(memory(first->kid->refs), statement(11).assignment(out, 0));
    }
    have out == observed by { close(); }
    have out == payload by { close(); }
    with(child_control(kid)) {
        have to_integer(count(child_ref(kid))) == 1 by { normalize(); }
        have to_integer(kid->refs) == 1 by {
            rewrite(to_integer(kid->refs), to_integer(count(child_ref(kid))));
            close();
        }
        have first->kid->refs == 1 by { rewrite(first->kid, kid); close(); }
        have exact(first->kid->refs) <= 1 by {
            have at(after_read, exact(first->kid->refs)) == first->kid->refs by { close(); }
            rewrite(exact(first->kid->refs), at(after_read, exact(first->kid->refs)));
            rewrite(at(after_read, exact(first->kid->refs)), first->kid->refs);
            rewrite(first->kid->refs, 1);
            close();
        }
    }
    step(parent_detach, { link: first_link });
    step();
    step();
    step();
    close();
}
```

```expect
pass
```
