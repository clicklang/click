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
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        solve();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            solve() using { 1 <= obj->refs; obj->refs != 1; };
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        solve();
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
    solve();
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
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have old(p->kid) == entry_child;
            open(child_control(p->kid)) { step_until(function.exit); }
            let link = fold(parent(p), { link: ParentLink::Linked(entry_child) });
            solve();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires 1 <= p->kid->refs;
    consumes child_control(p->kid);
    consumes child_ref(p->kid);
    if old(p->kid->refs) > 1 {
        produces child_control(old(p->kid));
    }
    produces p->kid;
    ensures old(p->kid->refs) > 1 implies old(p->kid)->payload == old(p->kid->payload);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have old(p->kid) == entry_child;
            have to_integer(old(p->kid->refs)) == to_integer(old(count(child_ref(p->kid))));
            step();
            have entry_child->refs == old(p->kid->refs);
            if entry_child->refs > 1 {
                have to_integer(old(count(child_ref(p->kid)))) > 1;
                step_until(function.exit);
                solve();
            } else {
                have to_integer(old(count(child_ref(p->kid)))) == to_integer(entry_child->refs);
                have to_integer(old(count(child_ref(p->kid)))) <= 1 by {
                    rewrite(to_integer(old(count(child_ref(p->kid)))) == to_integer(entry_child->refs));
                    solve();
                }
                step_until(function.exit);
                have to_integer(old(count(child_ref(p->kid)))) > 1 implies old(p->kid)->payload == old(p->kid->payload) by {
                    intro();
                    contradiction(to_integer(old(count(child_ref(p->kid)))) <= 1);
                }
                solve();
            }
        },
    }
}

int32 run_first_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { step(); solve(); } else {}
    fold(authority(child_ref(kid)));
    fold(child_storage(kid));
    step();
    unfold(child_storage(kid));
    fold(child_control(kid));
    step();
    step();
    branch { step(); step(); solve(); } else {}
    step();
    step();
    branch { step(); step(); step(); solve(); } else {}
    let { link: first_link } = step(parent_attach, {});
    let { link: second_link } = step(parent_attach, {});
    step(child_release, {});
    have first->kid == kid;
    have kid->payload == payload;
    open(child_control(kid)) {
        have to_integer(count(child_ref(kid))) > 1;
        have 2 <= to_integer(kid->refs) by {
            rewrite(to_integer(kid->refs) == to_integer(count(child_ref(kid))));
            solve();
        }
    }
    have first->kid->payload == payload by { rewrite(first->kid == kid); solve(); }
    have first->kid->refs == kid->refs by {
        normalize() using { first->kid == kid; };
    }
    have first->kid->refs > 1 by {
        rewrite(first->kid->refs == kid->refs);
        solve() using { 2 <= to_integer(kid->refs); };
    }
    mark detaching;
    step(parent_detach, { link: first_link });
    have at(detaching, first->kid) == kid by assumption();
    have at(detaching, first->kid)->payload == at(detaching, first->kid->payload) by {
        extract(at(detaching, first->kid)->payload == at(detaching, first->kid->payload));
        assumption();
    }
    have at(detaching, first->kid->payload) == payload by assumption();
    have at(detaching, first->kid)->payload == payload by {
        solve() using {
            at(detaching, first->kid)->payload == at(detaching, first->kid->payload);
            at(detaching, first->kid->payload) == payload;
        };
    }
    have kid->payload == payload by {
        have kid == at(detaching, first->kid) by { solve() using { at(detaching, first->kid) == kid; }; }
        rewrite(kid == at(detaching, first->kid));
        assumption();
    }
    step();
    have second->kid == kid;
    have second->kid->payload == payload by { rewrite(second->kid == kid); solve(); }
    mark reading;
    step(parent_read_payload, { link: second_link });
    have at(reading, second->kid->payload) == payload by assumption();
    have out == at(reading, second->kid->payload);
    have out == payload;
    have second->kid == kid;
    open(child_control(kid)) {
        have 1 <= to_integer(kid->refs) by {
            rewrite(to_integer(kid->refs) == to_integer(count(child_ref(kid))));
            solve();
        }
    }
    step(parent_detach, { link: second_link });
    step();
    step();
    step();
    solve();
}

int32 run_second_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { step(); solve(); } else {}
    fold(authority(child_ref(kid)));
    fold(child_storage(kid));
    step();
    unfold(child_storage(kid));
    fold(child_control(kid));
    step();
    step();
    branch { step(); step(); solve(); } else {}
    step();
    step();
    branch { step(); step(); step(); solve(); } else {}
    let { link: first_link } = step(parent_attach, {});
    let { link: second_link } = step(parent_attach, {});
    step(child_release, {});
    have second->kid == kid;
    have kid->payload == payload;
    open(child_control(kid)) {
        have to_integer(count(child_ref(kid))) > 1;
        have 2 <= to_integer(kid->refs) by {
            rewrite(to_integer(kid->refs) == to_integer(count(child_ref(kid))));
            solve();
        }
    }
    have second->kid->payload == payload by { rewrite(second->kid == kid); solve(); }
    have second->kid->refs == kid->refs by {
        normalize() using { second->kid == kid; };
    }
    have second->kid->refs > 1 by {
        rewrite(second->kid->refs == kid->refs);
        solve() using { 2 <= to_integer(kid->refs); };
    }
    mark detaching;
    step(parent_detach, { link: second_link });
    have at(detaching, second->kid) == kid by assumption();
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload) by {
        extract(at(detaching, second->kid)->payload == at(detaching, second->kid->payload));
        assumption();
    }
    have at(detaching, second->kid->payload) == payload by assumption();
    have at(detaching, second->kid)->payload == payload by {
        solve() using {
            at(detaching, second->kid)->payload == at(detaching, second->kid->payload);
            at(detaching, second->kid->payload) == payload;
        };
    }
    have kid->payload == payload by {
        have kid == at(detaching, second->kid) by { solve() using { at(detaching, second->kid) == kid; }; }
        rewrite(kid == at(detaching, second->kid));
        assumption();
    }
    step();
    have first->kid == kid;
    have first->kid->payload == payload by { rewrite(first->kid == kid); solve(); }
    mark reading;
    step(parent_read_payload, { link: first_link });
    have at(reading, first->kid->payload) == payload by assumption();
    have out == at(reading, first->kid->payload);
    have out == payload;
    have first->kid == kid;
    open(child_control(kid)) {
        have 1 <= to_integer(kid->refs) by {
            rewrite(to_integer(kid->refs) == to_integer(count(child_ref(kid))));
            solve();
        }
    }
    step(parent_detach, { link: first_link });
    step();
    step();
    step();
    solve();
}
