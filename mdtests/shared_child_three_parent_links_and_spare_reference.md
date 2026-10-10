# Three parent links and a spare child reference

Three parents each hold a link to a child. Reading the last link unfolds all
three parent resources in reverse parameter order, so the per-cell index of
`defined(p->kid)` facts must rebalance as it grows. Separately, a sharer that
requires its child's reference count to be two below `INT_MAX` calls a retain
helper requiring one below `INT_MAX`; the call precondition follows from an
order path that ends at a constant bound and is closed by comparing the two
constants. This catches a defined-read index that loses entries when it
rotates, and an order-path check that only accepts a path ending exactly at
the requested bound.

```c filename=shared_child_links.c
struct child { int32 refs; };
struct parent { struct child* kid; };
void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void share(struct child* obj) { child_retain(obj); }
struct child* last_kid(struct parent* a, struct parent* b, struct parent* c) { return c->kid; }
```

```click
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
        },
    }
}
authorized resource child_ref(obj: struct child*) {}
resource child_control(obj: struct child*) {
    owns *obj;
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}
verifying "shared_child_links.c";
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
void share(struct child* obj) {
    requires count(child_ref(obj)) < 2147483646;
    owns child_control(obj);
    produces child_ref(obj);
} by {
    step(child_retain(obj), {});
    step();
    simp();
}
struct child* last_kid(struct parent* a, struct parent* b, struct parent* c) {
    consumes c_link: parent(c);
    consumes b_link: parent(b);
    consumes a_link: parent(a);
    requires c_link.link != ParentLink::Empty;
    requires b_link.link != ParentLink::Empty;
    requires a_link.link != ParentLink::Empty;
    produces c->kid;
    produces b->kid;
    produces a->kid;
    ensures result == c->kid;
} by {
    match c_link.link {
        ParentLink::Empty => { contradiction(c_link.link == ParentLink::Empty); },
        ParentLink::Linked(ck) => {
            unfold(c_link);
            match b_link.link {
                ParentLink::Empty => { contradiction(b_link.link == ParentLink::Empty); },
                ParentLink::Linked(bk) => {
                    unfold(b_link);
                    match a_link.link {
                        ParentLink::Empty => { contradiction(a_link.link == ParentLink::Empty); },
                        ParentLink::Linked(ak) => {
                            unfold(a_link);
                            execute();
                            simp();
                        },
                    }
                },
            }
        },
    }
}
```

```expect
pass
```
